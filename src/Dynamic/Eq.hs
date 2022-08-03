{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module Dynamic.Eq where
import Dynamic.Ast
import Unbound.Generics.LocallyNameless
import Dynamic.Norm
import Control.Monad.Except

import Data.Map (Map)
import qualified Data.Map as Map

import Data.Set (Set)
import qualified Data.Set as Set
import GHC.Stack (HasCallStack)
import UnboundHelper
import PreludeHelper
import Dynamic.ElabBase
import Dynamic.Env
import Control.Monad.State
import AlphaShow (lfullshow)

--  A fancy eq would extract the definitional (erased) interpertation of terms 
-- would requires tracking the endpoints of path variables

-- interp :: Exp -> m (Set Exp)
-- interp = undefined

-- anyEq = undefined 
-- stuck  = undefined 
-- eq l info ty r = do
--   li <- interp l
--   ri <- interp r
--   if li `anyEq` ri
--   then pure $ Union l ty r
--   else stuck l info ty r 

-- for now at lest try to KEEP IT SIMPLE

-- eqNorm (Same l info ev r) = eq l info ev r
eqNorm e = norm (noNext{critN=eqNorm}) e




-- unionClean :: (Fresh m, WithDynDefs m) => Term -> Maybe Exp -> Term -> m Exp
-- unionClean l ty r = do
--   (me,_) <- runStateT (do
--     l' <- safeWhnf' l
--     r' <- safeWhnf' r
--     unionClean' l' ty r') 100
--   pure me

-- -- precondition l and r are alraedy whnf'ed (up to timeout)
-- unionClean' :: (Fresh m, WithDynDefs m, MonadState Integer m) => Term -> Maybe Exp -> Term -> m Exp
-- unionClean' (C l lc) Nothing r = unionClean' l (Just lc) r -- don't need to normalize l, since safeWhnf goes under C
-- unionClean' l Nothing (C r rc) = unionClean' l (Just rc) r
-- unionClean' (C l lc) (Just ty) r = unionClean' l (Just $ Union lc TyU ty) r
-- unionClean' l (Just ty) (C r rc) = unionClean' l (Just $ Union ty TyU rc) r
-- unionClean' l mty r | l `aeq` r = pure $ ecast l mty
-- unionClean' (Fun bndBodl) mty (Fun bndBodr) = do

--   ((ls,lx), bodl)<- unbind bndBodl
--   ((rs,rx), bodr)<- unbind bndBodr
--   bodl' <- safeWhnf' bodl
--   bodr' <- safeWhnf' $ subst rs (V ls) $  subst rx (V lx) bodr

--   bod <- unionClean' bodl' Nothing bodr'
--   pure $ ecast (Fun $ bind (ls,lx) bod) mty

-- -- unclear if this can be justified
-- -- unionClean' (fl `App` al) mty (fr `App` ar) = do 
-- --   f <- unionClean' fl Nothing fr
-- --   al' <- safeWhnf' al
-- --   ar' <- safeWhnf' ar
-- --   a <- unionClean' al' Nothing ar'
-- --   pure  $ ecast (f `App` a) mty

-- unionClean' (Pi al bndBodl) mty (Pi ar bndBodr) = do

--   al' <- safeWhnf' al
--   ar' <- safeWhnf' ar

--   a <- unionClean' al' Nothing ar'

--   (lx, bodl)<- unbind bndBodl
--   (rx, bodr)<- unbind bndBodl
--   bodl' <- safeWhnf' bodl
--   bodr' <- safeWhnf' $ subst rx (V lx) bodr

--   bod <- unionClean' bodl' Nothing bodr'
--   pure $ ecast (Pi a $ bind lx bod) mty

--   -- for  now cases need to match exactly
--   -- ...
-- -- unionClean' l  ty r  = 
-- --   case (l, r) of
-- --     (zipTConM (\l _ ev r -> unionClean' l (Just ev) r) -> Just ans) -> ans
-- --     (zipDConM (\l _ ev r -> unionClean' l (Just ev) r) (\l _ ev r ->  unionClean' l (Just ev) r) -> Just ans) -> ans
-- --     _ -> throwError ()




-- TODO depricate below
eq :: Fresh m => Term -> Info -> Exp -> Exp -> m Exp
eq l info ty r = runWithModuleMT (eqDef l info ty r) emptyModule

-- the term needs to equal up to some erasure
-- TODO , the  MonadError () m allows a "fail fast", that can remove a lot of branching in code
-- precondition called into whnf
eqrefl :: (Fresh m, WithDynDefs m, MonadError () m, MonadState Integer m) => Term -> Maybe Exp -> Exp -> m Exp
eqrefl (C l lc) Nothing r = eqrefl l (Just lc) r
eqrefl l Nothing (C r rc) = eqrefl l (Just rc) r
eqrefl (C l lc) (Just ty) r = eqrefl l (Just $ union lc TyU ty) r
eqrefl l (Just ty) (C r rc) = eqrefl l (Just $ union ty TyU rc) r
eqrefl l mty r | l `aeq` r = pure $ ecast l mty
eqrefl (Fun bndBodl) mty (Fun bndBodr) = do -- don't worry about eta for now

  ((ls,lx), bodl)<- unbind bndBodl
  ((rs,rx), bodr)<- unbind bndBodr
  bodl' <- safeWhnf' bodl
  bodr' <- safeWhnf' $ subst rs (V ls) $  subst rx (V lx) bodr

  -- loggg $ "Fun"
  -- loggg $ lfullshow bodl
  -- loggg $ lfullshow bodr
  -- loggg $ lfullshow bodl'
  -- loggg $ lfullshow bodr'
  -- loggg $ ""

  bod <- eqrefl bodl' Nothing bodr'
  pure $ ecast (Fun $ bind (ls,lx) bod) mty

eqrefl (fl `App` al) mty (fr `App` ar) = do 
  f <- eqrefl fl Nothing fr

  al' <- safeWhnf' al
  ar' <- safeWhnf' ar
  a <- eqrefl al' Nothing ar'
  pure  $ ecast (f `App` a) mty

eqrefl (Pi al bndBodl) mty (Pi ar bndBodr) = do

  al' <- safeWhnf' al
  ar' <- safeWhnf' ar

  a <- eqrefl al' Nothing ar'

  (lx, bodl)<- unbind bndBodl
  (rx, bodr)<- unbind bndBodl
  bodl' <- safeWhnf' bodl
  bodr' <- safeWhnf' $ subst rx (V lx) bodr

  bod <- eqrefl bodl' Nothing bodr'
  pure $ ecast (Pi a $ bind lx bod) mty

  -- for  now cases need to match exactly
  -- ...
eqrefl l  ty r  = 
  case (l, r) of
    (zipTConM (\l _ ev r -> eqrefl l (Just ev) r) -> Just ans) -> ans
    (zipDConM (\l _ ev r -> eqrefl l (Just ev) r) (\l _ ev r ->  eqrefl l (Just ev) r) -> Just ans) -> ans
    _ -> throwError ()

ecast :: Exp -> Maybe Exp -> Exp 
ecast e (Just ty) = C e ty
ecast e Nothing = e






-- interps :: (Fresh m, WithDynDefs m, MonadError () m, MonadState Integer m) => Term -> Maybe Exp -> Exp -> m Exp
-- interps







-- returns the sameness of teh 2 expresions embedded in the output expression
-- for instance 1 0 ->  1 ~ 0
-- 1 2 -> S( 0 ~ 1)
-- TODO (0 ~ 1)  (1 ~ 2) -> (0 ~ 1) U (1 ~ 2) 
-- normalization may be performed
eqDef :: (Fresh m, WithDynDefs m) =>
  Term -> Info -> Exp -> Exp -> m Exp
eqDef l info ty r = do
  -- loggg "eqDef"
  -- loggg $ lfullshow l
  -- loggg $ lfullshow r
  (me,_) <- runStateT (eqDef' l info ty r) 100
  -- loggg $ "me=" ++ lfullshow me
  pure me


eqDef' :: (MonadState Integer m, WithDynDefs m, Fresh m) =>
  Term -> Info -> Exp -> Exp -> m Exp
eqDef' (C l lc) info ty r = eqDef' l info (union lc TyU ty) r
eqDef' l info ty (C r rc) = eqDef' l info (union ty TyU rc) r
eqDef' l info ty r | l `aeq` r = pure $ C l ty -- redundent, but allows you to skip normalization sometimes
eqDef' l info ty r = do
  l' <- safeWhnf' l
  r' <- safeWhnf' r
  -- logg "eqdef'"
  -- loggg $ "r'=" ++  lfullshow r'
  -- loggg $ "l'=" ++ lfullshow l'
  -- loggg ""

  -- logg "getDefn' ... ="
  -- d <- getDefn' "first"
  -- logg d
  case (l', r') of
    -- injective moves
    (zipTConM (\l i ev r -> eqDef' l (tconInfo i info) ev r) -> Just ans) -> ans
    (zipDConM (\l i ev r -> eqDef' l (dconInfo i info) ev r) (\l i ev r -> eqDef' l (tconInfo i info) ev r) -> Just ans) -> ans
    _ -> do
      -- perhaps the terms line up (except for casts)
      me <- runExceptT $ eqrefl l' (Just ty) r'
      case me of
        Right e -> pure e
        _ -> pure $ Same l' info ty r'


-- --  a ptetty nasty way to do a pretty simple thing
-- shareOverlap :: (MonadState Integer m, WithDynDefs m, Fresh m) => [Exp] -> [Exp] -> Info -> [Exp] -> [Exp] -> m Bool
-- shareOverlap l (lrest)  _ _ (r:rrest) = do
--   l' <- safeWhnf' r
--   r' <- safeWhnf' r
--   case (l, r') of
--     (TyU,TyU) -> pure $ True
--     (TyU,r') -> shareOverlap 
-- -- shareOverlap = undefined


-- eq l r info ty = 
--   whnf $ Same l info ty r
-- eq l r info ty = 
--   case (l, r) of
--     (zipTCon (\l i ev r -> eq l r (tconInfo i info) ev) -> Just ans) ->  undefined 
--     _ -> undefined 
-- eq  l r info ty = 
-- eqAll 


-- zipTConM :: 
--   HasCallStack => 
--   (Exp -> Integer -> EqEv -> Exp -> Exp) -> (Term, Term) -> Maybe Term
-- zipTCon f ((TConF tCNamel indl (NoBnd _) tell), (TConF tCNamer indr (NoBnd _) telr))
--   | tCNamel == tCNamer = Just $ TConF tCNamel (zipTCon' f tell 0 indl indr) (NoBnd ()) tell
-- zipTCon _ _ = Nothing




-- zipDConM :: 
--   HasCallStack => 
--   (Exp -> Integer -> EqEv -> Exp -> Exp) -> 
--   (Exp -> Integer -> EqEv -> Exp -> Exp) -> (Term, Term) ->  Maybe Term
-- zipDCon f fty ((DConF dCNamel argl (tCNamel, NoBnd indl) tell teltyl), (DConF dCNamer argr (tCNamer, NoBnd indr) telr teltyr))
--   | dCNamel == dCNamer = let
--     ind =  (zipTCon' fty teltyl 0 indl indr)
--     in Just $ DConF tCNamel (zipTCon' f tell 0 argl argr) (tCNamel, NoBnd ind) tell teltyl
-- zipDCon _ _ _ = Nothing


-- zipTConM' :: 
--   HasCallStack => 
--   (Exp -> Integer -> EqEv -> Exp -> Exp) -> (Tel Exp Ty ()) -> Integer -> [Term] -> [Term] -> [Term]
-- zipTCon' f (TelBnd ty bndBod) i (l:lrest) (r:rrest) = let
--   otu = f l i ty r
--   in zipTCon' f (substBind bndBod otu) (i+1) lrest rrest
-- zipTCon' _ (NoBnd _) _ [] [] = []
-- zipTCon' _ _ _ _ _ = error "missmatch len"



-- eq conf TyU TyU info ty = pure $ C TyU ty

-- -- eq l r ty | l `aeq` r = pure $ Right $ C l ty
-- -- eq l r ty | sameCon l r == Just False = throwError (l,r)

-- eq conf l r info ty = undefined 

-- eq l r ty = do
--   l' <- safeWhnf 100 l -- TODO: pachage, since this isn't actually safe
--   r' <- safeWhnf 100 r
--   eq l' r' ty 

-- eq _ _ _ = undefined

-- how should
-- Refs
-- neutral terms
-- safety be handled