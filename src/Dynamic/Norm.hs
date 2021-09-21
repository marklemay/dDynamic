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

module Dynamic.Norm where

import GHC.Stack ( HasCallStack )


import Control.Applicative (Applicative (..), (<$>))
import Control.Monad (guard)
import Data.List (find)


import Data.Map (Map)
import qualified Data.Map as Map

import Data.Set (Set)
import qualified Data.Set as Set

import Data.Monoid (Any (..))
import Data.Typeable (Typeable)
import GHC.Generics (Generic, U1 (U1))
import Unbound.Generics.LocallyNameless
import Control.Monad.Except
import Unbound.Generics.LocallyNameless.Unsafe (unsafeUnbind)
import Control.Monad.Reader

import PreludeHelper
import UnboundHelper
import AlphaShow
import SourcePos

import Dynamic.Ast
import Dynamic.Env
import Dynamic.Err
import Dynamic.Erase


data YesNoStuck a --b
  = Yes a
  | No
  | Stuck --b
  deriving (Show)

-- sort of like neu
withPath :: Exp -> (Exp, Path)
withPath (C u info tu why ty) = let (e,p) = withPath u in (e, Trans p $ Step info why True tu ty)
--TODO could include Csym here
withPath e  = (e, Refl)




match :: 
  HasCallStack => 
  (Monad m) => 
  (Exp -> m Exp) -> (Exp -> m Exp) -> [(Exp,Pat)]
  -> m (YesNoStuck (Map Var Exp, Map PathVar Path))
match critN argN [] = pure $ Yes (Map.empty, Map.empty)
match critN argN ((e, PVar x):ms) = do 
  e' <- argN e
  xxx <- match critN argN ms
  pure $ case xxx of
    Yes (es, paths) -> Yes (Map.insert x e es, paths)
    No -> No
    Stuck -> Stuck
match critN argN ((e, Pat pv dcName pats): ms) = do 
  e' <- argN e
  case withPath e' of 
    (DConF dcName' _ _ , _) | dcName' /= dcName -> pure No
    (DConF dcName' args _, _) | length args /= length pats -> error "really broke bad lengths"
    (DConF dcName' args _, path) -> do
      xxx <- match critN argN (zip args pats ++ ms)
      pure $ case xxx of
        Yes (es, paths) -> Yes (es, Map.insert pv path paths)
        No -> No
        Stuck -> Stuck
        --   match critN argN (zip args pats ++ ms) bod
    _ -> pure Stuck -- TODO exposing the partial stuck state as a valid expression would allow for more definitional eqs, and possibly make the metatheory easier


matches ::
  HasCallStack => 
  (Fresh m) => 
  (Exp -> m Exp) -> (Exp -> m Exp) -> [Exp] -> [Match] -> m (Either ([Exp], [Match]) (Either Path Term))
matches critN argN scrutinees [] = pure $ Left (scrutinees, [])

  -- TODO inefficint since that scrutinee is recalculated every branch!
  -- TODO can simplify much more then currently
matches critN argN scrutinees ms@((Match bndbod):rest) = do
  (pats, (assign, bod)) <- unbind bndbod
  if length pats /= length scrutinees
    then error "diff len"
    else do 
    ans <- match critN argN (zip scrutinees pats) --TODO need a monadically safe zip with HasCallStack and a good error message
    case ans of
      Yes (es, ps) -> do
        logg $ "matched on"
        logg $ pats
        logg $ scrutinees
        logg $ ps
        logg $ es
        logg $ ""
        pure $ Right $ substs (Map.toList ps) $ substs (Map.toList es) $ bod
      No -> matches critN argN scrutinees rest
      Stuck -> pure $ Left (scrutinees, ms)

mapInjTcon :: HasCallStack => (Fresh m, WithDynDefs m) => (Exp -> m Exp) -> Path -> Integer -> m Path
mapInjTcon _ Refl _ = pure Refl
mapInjTcon crit (Step info w d l r) i = do
  w' <- crit w
  l' <- crit l
  r' <- crit r
  case (w', l', r') of
   ((TConF tCNameW argW _), (TConF tCNamel argl _), (TConF tCNamer argr _)) 
     | tCNamel == tCNamer && tCNamel == tCNameW 
       && length argl == length argr && length argl == length argW 
       && fromIntegral i < length argl --TODO: might break in partially applied situtations?
     -> pure $ Step (obsmap (Index i) info) (argW !! fromIntegral i) d (argl !! fromIntegral i) (argr !! fromIntegral i)
   _ -> pure $ InjTcon (Step info w' d l' r') i
mapInjTcon crit (Sym p) i = Sym <$> mapInjTcon crit p i 
mapInjTcon crit (Trans l r) i = do
  l' <- mapInjTcon crit l i
  r' <- mapInjTcon crit r i
  pure $ Trans l' r'
mapInjTcon _ (Debug s) i = pure $ Debug $ s ++ "." ++ show i
mapInjTcon _ p i = pure $ InjTcon p i


mapInjDcon :: HasCallStack => (Fresh m, WithDynDefs m) => (Exp -> m Exp) -> Path -> Integer -> m Path
mapInjDcon _ Refl _ = pure Refl
mapInjDcon crit (Step info w d l r) i = do
  w' <- crit w
  l' <- crit l
  r' <- crit r
  case (w', l', r') of
   (withPath -> (DConF tCNameW argW _, _), withPath -> (DConF tCNamel argl _, _), withPath -> (DConF tCNamer argr _, _)) 
       --throwing away the path info, TODO this is likely a little buggy
     | tCNamel == tCNamer && tCNamel == tCNameW 
       && length argl == length argr && length argl == length argW 
       && fromIntegral i < length argl --TODO: might break in partially applied situtations?
     -> pure $ Step (obsmap (Index i) info) (argW !! fromIntegral i) d (argl !! fromIntegral i) (argr !! fromIntegral i)
   _ -> pure $ InjTcon (Step info w' d l' r') i
mapInjDcon crit (Sym p) i = Sym <$> mapInjDcon crit p i 
mapInjDcon crit (Trans l r) i = do
  l' <- mapInjDcon crit l i
  r' <- mapInjDcon crit r i
  pure $ Trans l' r'
mapInjDcon _ (Debug s) i = pure $ Debug $ s ++ "." ++ show i
mapInjDcon _ p i = pure $ InjDcon p i


-- TODO add simp?
normPath :: HasCallStack => (Fresh m, WithDynDefs m) => (Exp -> m Exp) -> Path -> m [Path]
normPath crit  (PathV v ann) = pure $ [PathV v ann]
normPath crit  (Step info w d l r) = do
  l' <- crit l  
  r' <- crit r  
  w' <- crit w 
  pure $ [Step info w' d l' r']
normPath crit  (Refl) = pure $ []
normPath crit  (Trans l r) = do
  l' <- normPath crit  l 
  r' <- normPath crit  r
  pure $ l' ++ r'
normPath crit  (Sym p) = do
  ps <- normPath crit  p 
  pure $ fmap rev $ reverse ps
normPath crit  (InjTcon p i) = do
  ps <- normPath crit  p
  mapM (\ pp -> mapInjTcon crit pp i) ps
normPath crit  (InjDcon p i) = do
  ps <- normPath crit  p
  mapM (\ pp -> mapInjDcon crit pp i) ps

norm :: HasCallStack => (Fresh m, WithDynDefs m) => (Exp -> m Exp) -> (Exp  -> m Exp) -> Exp -> m Exp
norm crit simp (V x ann) = do -- expand module deffinitions,, TODO can facrtor this out like in the prevous attempt
   me <- getDefnm' x
   case me of
     Just e -> crit e
     Nothing -> pure $ V x ann

norm crit simp (Csym trm path bndty ann) = do
  -- logg "Csym"
  paths <- normPath crit path
  casts <- forM paths $ \ p -> do
    -- logg "path"
    -- logg p
    case p of
      Step info w d l r -> do
        (x, ty) <- unbind bndty
        ety <- eraseCast ty
        why <- norm crit simp $ subst x w ety

        lty <- norm crit simp $ substBind bndty l
        rty <- norm crit simp $ substBind bndty r
        
        pure $ \ under -> C under info lty why rty
      compositepath -> pure $ \ under -> Csym under compositepath bndty (An $ substBind bndty <$> snd <$> endpoints compositepath)
  -- filter out Casts with no content
  -- casts' <- filterM (\ (_, bndty)-> do
  --   (px, ty) <- unbind bndty
  --   pure $ occursIn px ty) casts
  trm' <- crit trm
  pure $ foldl (\ e c -> c e) trm' casts

norm crit simp (Same (under -> Just l) obs r) = crit (Same l obs r)
norm crit simp (Same l obs (under -> Just r)) = crit (Same l obs r)

norm crit simp (Same l obs r) = do
  l' <- crit l
  r' <- crit r 
  case (l', r') of
    (TyU, TyU) -> pure TyU

    (TConF tCNamel argsl _, TConF tCNamer argsr _) | tCNamel == tCNamer && length argsl == length argsr -> do
      args <- mapM (\ (i, ll, rr) -> simp (Same ll (obsmap (Index i) obs) rr)) $ zip3 [0..] argsl argsr
      pure $ TConF tCNamel args noAn

    (DConF dCNamel argsl _, DConF dCNamer argsr _)  | dCNamel == dCNamer && length argsl == length argsr  -> do
      args <- mapM (\ (i, ll, rr) -> simp (Same ll (obsmap (Index i) obs) rr)) $ zip3 [0..] argsl argsr
      pure $ DConF dCNamel args noAn

    (Pi aTyl bndbodTyl, Pi aTyr bndbodTyr) -> do
      (argnamel, bodl) <- unbind bndbodTyl --TODO unbind2 ?
      (argnamer, bodr) <- unbind bndbodTyr
      aTy <- simp (Same aTyl (obsmap Aty obs) aTyr)
      bodTy <- simp (Same bodl (obsmap (Bty (v argnamel)) obs) $ subst argnamer (v argnamel) bodr)

      pure $ Pi aTy $ bind argnamel bodTy -- TODO rename or swap would be better
    
    (Fun bndbodl _, Fun bndbodr _) -> do
      ((selfl, argnamel), bodl) <- unbind bndbodl
      ((slefr, argnamer), bodr) <- unbind bndbodr
      -- logg ""
      -- logg bodl
      -- logg bodr
      bod <- simp (Same bodl (obsmap (AppW (v argnamel)) obs) $ subst slefr (v selfl) $ subst argnamer (v argnamel) bodr)
      -- logg bod
      -- logg ""
      pure $ Fun (bind (selfl, argnamel) bod) noAn

    _ -> pure $ Same l' obs r'


norm crit simp (C trm info uty why ty) = do
  uty' <- crit uty
  why' <- crit why 
  ty' <- crit ty
  case (uty', ty') of
    (TyU, TyU) -> crit trm -- TODO can be blocked by why' ?
    _ -> do 
      trm' <- simp trm
      pure $ C trm' info uty' why' ty'


norm crit simp (App f a an) = do
  -- logg "App"
  f' <- crit f
  case f' of
    Fun bndbod _ -> do
      ((fname, aname), bod) <- unbind bndbod
      crit $ subst aname a $ subst fname f' bod
    
    TConF tCName args (An Nothing) -> do
      args' <- mapM simp $ args ++ [a]
      pure $ TConF tCName args' noAn
    TConF tCName args (An (Just (TelBnd _ bndrestTel))) -> do
      args' <- mapM simp $ args ++ [a]
      pure $ TConF tCName args' $ ann $ substBind bndrestTel a -- TODO normaliza annotation

    DConF dCName args (An Nothing) -> do
      args' <- mapM simp $ args ++ [a]
      pure $ DConF dCName args' noAn
    DConF dCName args (An (Just (tCName, TelBnd _ bndrestTel))) -> do -- assumes casts are already made
      args' <- mapM simp $ args ++ [a]
      pure $ DConF dCName args' $ ann (tCName, substBind bndrestTel a) -- TODO normaliza annotation

    C u info uty w t -> do
      case (uty, w, t) of

        (Pi aTy' bndbodTy', Pi aTyw bndbodTyw, Pi aTy bndbodTy) -> do
          -- logg "commute"
          let ac = C a info aTy aTyw aTy' -- TODO swap the why?
          let underTy = substBind bndbodTy' ac
          let under = App u ac $ ann underTy
          crit $ C under info underTy (substBind bndbodTyw a) (substBind bndbodTy a)
        (_, w, t) -> do
          w' <- simp w
          u' <- simp u 
          uTy' <- simp uty 
          t' <- simp t 
          a' <- simp a
          -- an' <- mapM simp an
          -- logg "TODO simp ann" 
          pure $ App (C u' info uTy' w' t') a' an -- TODO is it concievealbe that the entire cast is simplified out, but it didn't crtit out?
    -- can normalize Csym just find

    _ -> do
      a' <- simp a
      -- an' <- mapM simp an
      -- logg "TODO simp ann" 
      pure $ App f' a' an


norm crit simp (Case scrutinees ann branches l outTy) = do
  scrutinees' <- mapM crit scrutinees -- TODO could be tighter, only normalize the scruts that can be tested 
  
  ans <- matches crit simp scrutinees branches
  case ans of
    Right (Left _)  -> error "get srtuck with the contrediction"
    Right (Right e) -> crit e
    Left (scrutinee', branches') -> do
      branches'' <- mapM (\ (Match bndBod) -> do (pat, bod') <- unbind bndBod; pure $ Match $ bind pat bod') branches' -- TODO simp
      pure $ Case scrutinee' ann branches'' l outTy

norm crit simp (DConF dCName params an) = do
  params' <- mapM simp params
  -- logg "TODO simp ty ann" 
  pure $ DConF dCName params an
norm crit simp (TConF dCName params an) = do
  params' <- mapM simp params
  -- logg "TODO simp ann" 
  pure $ TConF dCName params an
norm crit simp (Pi aty bndBodTy) = do
  aty' <- simp aty
  (aName, bodTy) <- unbind bndBodTy
  bodTy' <- simp bodTy
  pure $ Pi aty' $ bind aName bodTy'
  
norm crit simp (Fun bndBod ann) = do
  -- logg "TODO simp ann" 
  ((fname,aName), bod) <- unbind bndBod
  bod' <- simp bod
  pure $ Fun (bind (fname,aName) bod') ann


norm crit simp TyU = pure TyU
norm crit simp e = do logg $ "not done yet" ++ show e ; pure e


normClean (C u info botTy whyTy topTy) = do
  botTy' <- normClean botTy -- TODO this should be a safe cleaning call-by-value
  topTy' <- normClean topTy -- TODO this should be a safe cleaning call-by-value
  if botTy' `aeq` topTy' 
    then normClean u
    else do
      u' <- normClean u
      pure $ C u' info botTy' whyTy topTy'
normClean (Csym (u @ (tyInf -> Just botTy)) p inThis (An (Just topTy))) = do
  botTy' <- normClean botTy -- TODO this should be a safe cleaning call-by-value
  topTy' <- normClean topTy -- TODO this should be a safe cleaning call-by-value
  if botTy' `aeq` topTy' 
    then normClean u
    else do
      u' <- normClean u
      pure $ Csym u' p inThis (An (Just topTy'))
normClean  e = norm normClean normClean e

whnf :: (Fresh m, WithDynDefs m) => Exp -> m Exp
whnf = norm whnf pure


whnfann :: (Fresh m, WithDynDefs m) => Exp -> m Exp
-- whnfann (C trm uty why ty) = do
--   ty' <- whnf ty
--   pure $ C trm uty why ty'
whnfann (App f a (An (Just ty))) = do
  ty' <- whnf  ty
  pure $ App f a (An (Just ty'))
whnfann (Case s m b l (An (Just ty))) = do
  ty' <- whnf ty
  pure $ Case s m b l (An (Just ty'))
whnfann x = pure x -- everything else already in whnf

-- TODO this name isn't great
cbvCheck :: HasCallStack =>
  (MonadError Err m, Fresh m, WithDynDefs m) => 
  Term -> m Exp
cbvCheck (Same l info r) | sameCon l r == Just False = do
  throwInfoError (show (e l) ++ "=/=" ++ show (e r)) info
cbvCheck (e@(Same l info r)) = do
  norm cbvCheck cbvCheck e -- probly aslight overcorrection
cbvCheck (App f a ann) = do
  f' <- cbvCheck f
  a' <- cbvCheck a
  -- TODO check that a is a value!
  norm cbvCheck pure $ App f' a' ann --TODO some redundant computation... but the definition is at least tight
cbvCheck (C u info uTy w t) = do
  u' <- cbvCheck u
  w' <- cbvCheck w 
  uTy' <- cbvCheck uTy
  t' <- cbvCheck t
  pure u'
  -- if uTy' `aeq` t' -- can lose out on some error messages, but fine
  --   then pure u'
  --   else pure $ C u' info uTy' w' t'
cbvCheck (TConF tCName args an) = do
  args' <- mapM cbvCheck args
  pure $ TConF tCName args an
cbvCheck (DConF dCName args an) = do
  args' <- mapM cbvCheck args
  pure $ DConF dCName args an
cbvCheck (Case scruts anTel branches sr ann) = do
  scruts' <- mapM cbvCheck scruts
  
  -- logg $ "scruts"
  -- loggg $ lfullshow scruts
  -- logg $ scruts
  -- logg $ scruts'
  norm cbvCheck pure $ Case scruts' anTel branches sr ann
cbvCheck (e@(Fun _ _)) = pure e -- TODO should probly still simplify for readability
cbvCheck (Pi aTy bodTy) = do
  aTy' <- cbvCheck aTy
  pure $ Pi aTy' bodTy -- TODO should probly still simplify for readability

cbvCheck e = do
  -- logg "norm cbvCheck pure e"
  norm cbvCheck pure e



whnfCheck :: (Fresh m, MonadError Err m, WithDynDefs m) => Exp -> m Exp
-- whnfCheck (Same l info r) | sameCon l r == Just False = 
--   throwInfoError (show (e l) ++ "=/=" ++ show (e r)) info
  -- error "throw info error"
  -- runWithSourceLocMT (throwPrettyError $ "because " ++ show o ++ ", " ++ show (e l) ++ "=/=" ++ show (e r)) $ Just src
-- whnfCheck e = norm whnfCheck whnfCheck pure e
whnfCheck e = error " .... "


isCon :: Exp -> Bool
isCon TyU = True
isCon (Pi _ _) = True
isCon (Fun _ _) = True
isCon (tConPat -> Just _) = True
isCon (DConF _ _ _) = True --TODO: not exactly right
isCon _ = False

sameCon :: Exp -> Exp -> Maybe Bool
sameCon TyU TyU = Just True
sameCon (tConPat -> Just (s1, _)) (tConPat -> Just (s2, _)) | s1 == s2 = Just True
sameCon (DConF s1 _ _) (DConF s2 _ _) | s1 == s2 = Just True
sameCon (Fun _ _) (Fun _ _) = Just True
sameCon (Pi _ _) (Pi _ _) = Just True
sameCon e1 e2 | isCon e1 && isCon e2 = Just False
sameCon _ _ = Nothing 
