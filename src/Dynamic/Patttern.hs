{-# LANGUAGE ViewPatterns, DeriveDataTypeable, DeriveGeneric, MultiParamTypeClasses, FlexibleContexts, FlexibleInstances, DeriveFunctor, RankNTypes, LambdaCase  #-}
{-# LANGUAGE DoAndIfThenElse #-}

{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
-- | manipulate collections of patterns
module Dynamic.Patttern where


import Data.Map (Map)
import qualified Data.Map as Map


import Dynamic.Ast
import Dynamic.ElabBase
import Control.Monad
import UnboundHelper
import Unbound.Generics.LocallyNameless

import AlphaShow
import PreludeHelper

import Control.Monad.Logic
import Control.Applicative
import MonadTransformers

-- TODO since this can be slow (eponentially) in the worst case we should not do it much in the elaboration phase, instead warn and clean, as with other slow operations

-- these operations assume pattern vars are unique
-- subAll [pat] [pat] 
subAll bases (s:remove) = do
  (concat -> bases') <- mapM (\ b -> fst <$> subPats' b s  ) bases 
  subAll bases' remove
subAll bases [] = pure bases




-- remove the overlap from a pattern, results in a list of patterns ORed together and an ORed list of the patterns removed
-- subPat :: Pat -> Pat -> [Pat]
subPat pat (PVar _) = pure ([],[pat])
subPat pat@(Pat dCName _ _) sub@(Pat dCName' _ _) | dCName /= dCName' = 
  pure ([pat], [])
subPat pat@(Pat dCName args path) sub@(Pat dCName' args' _) -- possible overlap
  | dCName == dCName' && length args == length args' = do

    (remaining, removed) <- subPats $ zip args args'

    pure (Pat dCName <$> remaining <*> pure path,  Pat dCName <$> removed <*> pure path)
subPat (PVar _) sub@(Pat dCName args pv) = do -- overlap.
    (tCName,_) <- getConsTcon dCName
    DataDef _ con@(Map.toList -> cons) <- getDatadef tCName

    refinedvar <- forM cons $ \ (dCName', tel) -> do
      args' <- fillFresh tel
      pv' <- fresh pv
      pure (dCName', Pat dCName' args' pv')

    let [(_,match)] = filter (\(x,_) -> x == dCName) refinedvar -- know there is exactly 1

    -- loggg $ lfullshow match

    (kept,removed) <- subPat match sub
    -- loggg $ lfullshow kept

    let removedFromVar = filter (\(x,_) -> x /= dCName) refinedvar

    pure (kept ++ (snd <$> removedFromVar), removed)


-- remove the overlap from a pattern list, results in a list of (list of) patterns ORed together and an ORed list of the (list of) patterns removed
subPats ((base, remove):rest) = do
  (remaining, removed) <- subPat base remove
  (remainingList, removelist) <- subPats rest
  
  -- loggg $ "remaining= "
  -- loggg $ lfullshow remaining
  -- loggg $ "removed= "
  -- loggg $ lfullshow removed
  -- loggg $ "remainingList= "
  -- loggg $ lfullshow remainingList
  -- loggg $ "removelist= "
  -- loggg $ lfullshow removelist
  -- loggg $ ""


  let theseCases = combo remaining removelist 

  let complimentaryCasess = (base:) <$> remainingList
  -- can use the sub to refine, this is a little less efficient and type scary. though it does provide more patterns
  -- let complimentaryCasess = combo (removed ++ remaining) remainingList
 
  let removelist' = combo removed removelist

  -- pure $ Just (rrr ++ remainingcombos, remove : removelist)
  pure (theseCases ++ complimentaryCasess, removelist') 

subPats [] = pure ([], [[]]) 

subPats' l r = subPats $ zip l r

-- | create a free pattern from a telescope, with a var for each binding
-- uses names on binder names for var creation
fillFresh :: (Alpha a, Alpha b, Fresh f) => Tel Term a b -> f [Pat]
fillFresh (NoBnd _) = pure []
fillFresh (TelBnd _ bndRestTel) = do 
  (x, restTel) <- unbind bndRestTel
  ls <- fillFresh restTel
  pure $ (PVar x) :ls




-- is the left pattern completly contains the right pattern
patContains :: Pat -> Pat -> Maybe (Map Var Pat)
patContains p (PVar x) = Just $ Map.fromList [(x,p)] 
patContains (Pat dCName args path) (Pat dCName' args' _) -- possible overlap
  | dCName == dCName' && length args == length args' = do
    patsContains $ zip args args'
patContains _ _ = Nothing 

-- for each pairwise tuple, the pattern on the left is contained by the pattern on the right
patsContains :: [(Pat, Pat)] -> Maybe (Map Var Pat)
patsContains [] = Just Map.empty 
patsContains ((l,r) : rest)= do
  h <- patContains l r 
  t <- patsContains rest
  Just $ Map.union h t 


-- if i had more guts this maybe would be a throw
-- subPats :: [(Pat,Pat)] -> ([Pat],[Pat])
-- subPats ((base, remove):rest) = do
--   (remaining, removed) <- subPat base remove
--   case remaining of
--     [] -> pure Nothing -- no overlap
--     _ -> do
--       mrest <- subPats rest
--       case mrest of
--         Nothing -> pure Nothing
--         Just (remainingList, removelist) -> do 

--           let theseCases = combo remaining removelist
--           let complimentaryCasess = combo removed remainingList

--           let removelist' = combo removed removelist

--           -- pure $ Just (rrr ++ remainingcombos, remove : removelist)
--           undefined 

-- dedupPat ::  [Pat] -> [Pat]
-- dedupPat 



-- TODO this code is confusing since lists mean either disjunction in removePat or a tuple in removePatsPar




-- take an underliging collection of patterns (OR) and remove one pattern from it, leaving a collection of new patterns that will not overlap with eachother
-- if the origional patterrns do not overlap the resulting patterns will not overlap
-- ignores the path var
removePat _ (PVar _) = pure [] -- completely coverd
removePat (pat@(Pat dCName args _):rest) sub@(Pat dCName' _ _) | dCName /= dCName' = do -- no overlap
  rest' <- removePat rest sub
  pure $ pat : rest'
removePat (Pat dCName args path:rest) sub@(Pat dCName' args' _) -- possible overlap
  | dCName == dCName' && length args == length args' = do
    
    -- logg $ "removePatsPar " ++ show args ++ " " ++ show args' 
    argss <- removePatsPar args args'
    -- logg $ "removePat " ++ show rest ++ " " ++ show sub 
    rest' <- removePat rest sub
    let out = ((Pat dCName) <$> argss <*> pure path) ++ rest'
    -- logg $ "out = " ++ show out
    pure out
removePat ((PVar _):rest) sub@(Pat dCName args pv) = do -- overlap. ( since var covers everythin, we can skip over the rest?)
    (tCName,_) <- getConsTcon dCName
    DataDef _ (Map.toList -> cons) <- getDatadef tCName
    splits <- forM cons $ \ (dCName', tel) -> do
      args' <- fillFresh tel
      pv' <- fresh pv
      pure $ Pat dCName' args' pv'
    -- logg $ "splits = " ++ show splits
    -- -- removePat (splits ++ rest) sub
    -- logg $ "removePat " ++ show splits ++ " " ++ show sub
    removePat splits sub
removePat [] _ = pure []
removePat a@(Pat dCName args _:rest) sub@(Pat dCName' args' _) -- possible overlap, but incorrect ag lengs
  | dCName == dCName' && length args /= length args' = error $ "bad len, removePat " ++ show a ++ " " ++ show sub


getOverlapsLs ((base,remove): rest) = do
  undefined

-- if any elem fails to remove, then can short circut the entire thing
removePatLs' ((base,remove): rest) = do
  e <- removePat [base] remove
  if e `aeq` [base]
  then pure $ []
  else do


    undefined



-- TODO rename removePatsArgs? removePatsList?
-- subtract each pattern pairwise, where this is a sequence of patternss
removePatsPar h s | length h == length s = do
  -- logg $ "removePatsPar " ++ show h ++ " " ++ show s
  (ans, _) <- removePatsPar' $ zip h s
  pure ans
removePatsPar _ _ = error "unequal len"


-- wildly inefficient, but more granular patterns help the unifier out.... so why not?
removePatsPar' ((h,s):rest) = do
  (restAns,restHirez) <- removePatsPar' rest
  -- logg $ "removePat " ++ show [h] ++ " " ++ show s
  some <- removePat [h] s
  -- logg $ "some = " ++ show some
  
  -- logg $ "restHirez = " ++ show (restHirez)
  -- logg $ "combo some restHirez = " ++ show (combo some restHirez)

  -- logg $ "combo some restHirez ++ (fmap (s:) restAns)  = " ++ show (combo some restHirez ++ (fmap (s:) restAns) )

  pure (combo some restHirez ++ (fmap (s:) restAns), combo (s:some) restHirez)
removePatsPar' [] = pure ([],[[]]) -- TODO right?



-- removePats orig [] = pure orig
-- removePats (orig:orest) (x :rest) = do
--   rem <- removePatsPar orig x
--   rem' <- removePats orest (x :rest)
--   removePats (rem ++ rem')  rest
-- removePats [] _ = pure []


-- append every combination of the first list onto the front of the 2nd
--combo [1..4] [[0,-1],[-2,-3]]
-- [[1,0,-1],[1,-2,-3],[2,0,-1],[2,-2,-3],[3,0,-1],[3,-2,-3],[4,0,-1],[4,-2,-3]]
-- TODO a more std way to do this?
combo :: [a] -> [[a]] -> [[a]]
combo [] _ = []
combo (h:rest) ls = fmap (h:) ls ++ combo rest ls




-- TODO move other pattern halper funcs here

-- TODO backport explanations to Ty.hs
-- TESTING (TODO move to test swaet)

x  = s2n "x"
te  = TelBnd TyU $ bind x $ TelBnd (V x) $ u $ NoBnd TyU

te1 = runFreshM $ fillFresh te 




boolVec :: (Eq t, Num t) => t -> [[Bool]]
boolVec i | i == 0 = [[]]
boolVec i  = do 
  h <- [True, False]
  t <- boolVec (i-1 )
  pure $ h : t

boolPatVec :: (MonadLogic m, Fresh m, Eq t, Num t) => t -> m [Pat]
boolPatVec i | i == 0 = pure []
boolPatVec i  = do 
  px <- fresh $ s2n "px"
  wild <- fresh $ s2n "_"
  h <- choose [Pat "t" [] px, Pat "f" [] px, PVar wild]
  t <- boolPatVec (i-1 )
  pure $ h : t


-- pe0 = runLogicT $ runFreshMT $ boolPatVec 3
pe0 = runFreshM $ observeManyT 10 (boolPatVec 3) 


-- ehostiveTest i = do
--   v <- boolPatVec i
--   v' <- boolPatVec i

--   undefined


choose :: (Alternative f) => [a] -> f a
choose = foldr ((<|>) . pure) empty
-- feel like I've done this before... and it worked poorly?




