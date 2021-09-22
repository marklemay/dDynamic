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
        -- logg $ "matched on"
        -- logg $ pats
        -- logg $ scrutinees
        -- logg $ ps
        -- logg $ es
        -- logg $ ""
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

-- norm :: HasCallStack => (Fresh m, WithDynDefs m) => (Exp -> m Exp) -> (Exp  -> m Exp) -> Exp -> m Exp
norm :: (WithDynDefs m, Fresh m) =>
  (Term -> m Exp)
  -> (Exp -> m Term) -> (Exp -> Info -> Exp -> m Exp) -> Exp -> m Exp
norm crit simp check (V x ann) = do -- expand module deffinitions,, TODO can facrtor this out like in the prevous attempt
   me <- getDefnm' x
   case me of
     Just e -> crit e
     Nothing -> pure $ V x ann

norm crit simp check (Csym trm path bndty ann) = do
  -- logg "Csym"
  paths <- normPath crit path
  casts <- forM paths $ \ p -> do
    -- logg "path"
    -- logg p
    case p of
      Step info w d l r -> do
        (x, ty) <- unbind bndty
        ety <- eraseCast ty
        why <- norm crit simp check $ subst x w ety

        lty <- norm crit simp check $ substBind bndty l
        rty <- norm crit simp check $ substBind bndty r
        
        pure $ \ under -> C under info lty why rty
      compositepath -> pure $ \ under -> Csym under compositepath bndty (An $ substBind bndty <$> snd <$> endpoints compositepath)
  -- filter out Casts with no content
  -- casts' <- filterM (\ (_, bndty)-> do
  --   (px, ty) <- unbind bndty
  --   pure $ occursIn px ty) casts
  trm' <- crit trm
  pure $ foldl (\ e c -> c e) trm' casts

norm crit simp check (Same (under -> Just l) obs r) = crit (Same l obs r)
norm crit simp check (Same l obs (under -> Just r)) = crit (Same l obs r)

norm crit simp check (Same l obs r) = do
  l' <- crit l
  r' <- crit r 
  -- loggg $ lfullshow l'
  -- loggg $ lfullshow r'
  case (l', r') of
    (TyU, TyU) -> pure TyU

    (TConF tCNamel argsl _, TConF tCNamer argsr _) | tCNamel == tCNamer && length argsl == length argsr -> do
      args <- mapM (\ (i, ll, rr) -> check ll (obsmap (Index i) obs) rr) $ zip3 [0..] argsl argsr
      pure $ TConF tCNamel args noAn

    (DConF dCNamel argsl _, DConF dCNamer argsr _)  | dCNamel == dCNamer && length argsl == length argsr  -> do
      args <- mapM (\ (i, ll, rr) -> check ll (obsmap (Index i) obs) rr) $ zip3 [0..] argsl argsr
      pure $ DConF dCNamel args noAn

    (Pi aTyl bndbodTyl, Pi aTyr bndbodTyr) -> do
      (argnamel, bodl) <- unbind bndbodTyl --TODO unbind2 ?
      (argnamer, bodr) <- unbind bndbodTyr
      aTy <- check aTyl (obsmap Aty obs) aTyr
      bodTy <- check bodl (obsmap (Bty (v argnamel)) obs) $ subst argnamer (v argnamel) bodr

      pure $ Pi aTy $ bind argnamel bodTy -- TODO rename or swap would be better
    
    (Fun bndbodl _, Fun bndbodr _) -> do
      ((selfl, argnamel), bodl) <- unbind bndbodl
      ((slefr, argnamer), bodr) <- unbind bndbodr
      -- logg ""
      -- logg bodl
      -- logg bodr
      bod <- check bodl (obsmap (AppW (v argnamel)) obs) $ subst slefr (v selfl) $ subst argnamer (v argnamel) bodr
      -- logg bod
      -- logg ""
      pure $ Fun (bind (selfl, argnamel) bod) noAn

    _ -> check l' obs r'


norm crit simp check (C trm info uty why ty) = do
  uty' <- crit uty
  why' <- crit why 
  ty' <- crit ty
  case (uty', why', ty') of
    (TyU, TyU, TyU) -> crit trm -- TODO can be blocked by why' ?
    _ -> do 
      trm' <- simp trm
      pure $ C trm' info uty' why' ty'


norm crit simp check (App f a an) = do
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


norm crit simp check (Case scrutinees ann branches l outTy) = do
  scrutinees' <- mapM crit scrutinees -- TODO could be tighter, only normalize the scruts that can be tested 
  
  ans <- matches crit simp scrutinees branches
  case ans of
    Right (Left _)  -> error "get srtuck with the contrediction"
    Right (Right e) -> crit e
    Left (scrutinee', branches') -> do
      branches'' <- mapM (\ (Match bndBod) -> do (pat, bod') <- unbind bndBod; pure $ Match $ bind pat bod') branches' -- TODO simp
      pure $ Case scrutinee' ann branches'' l outTy

norm crit simp check (DConF dCName params an) = do
  params' <- mapM simp params
  -- logg "TODO simp ty ann" 
  pure $ DConF dCName params an
norm crit simp check (TConF dCName params an) = do
  params' <- mapM simp params
  -- logg "TODO simp ann" 
  pure $ TConF dCName params an
norm crit simp check (Pi aty bndBodTy) = do
  aty' <- simp aty
  (aName, bodTy) <- unbind bndBodTy
  bodTy' <- simp bodTy
  pure $ Pi aty' $ bind aName bodTy'
  
norm crit simp check (Fun bndBod ann) = do
  -- logg "TODO simp ann" 
  ((fname,aName), bod) <- unbind bndBod
  bod' <- simp bod
  pure $ Fun (bind (fname,aName) bod') ann


norm crit simp check TyU = pure TyU
norm crit simp check e = do logg $ "not done yet" ++ show e ; pure e

normClean :: (WithDynDefs m, Fresh m) => Ty -> m Term
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
normClean (TConF tCName args an) = do
  args' <- mapM normClean args
  pure $ TConF tCName args an
normClean (DConF dCName args an) = do
  args' <- mapM normClean args
  pure $ DConF dCName args an
normClean e = norm normClean normClean differ e

whnf :: (Fresh m, WithDynDefs m) => Exp -> m Exp
whnf = norm whnf pure noCheck


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



cbv check (App f a ann) = do
  f' <- cbv check  f
  a' <- cbv check  a
  norm (cbv check) pure check $ App f' a' ann
cbv check  (C u info uTy w t) = do
  u' <- (cbv check) u
  w' <- (cbv check) w 
  uTy' <- (cbv check) uTy
  t' <- (cbv check) t
  if uTy' `aeq` t' -- can lose out on some error messages, but fine
    then pure u'
    else pure $ C u' info uTy' w' t'
cbv check (TConF tCName args an) = do
  args' <- mapM (cbv check) args
  pure $ TConF tCName args an
cbv check (DConF dCName args an) = do
  args' <- mapM (cbv check) args
  pure $ DConF dCName args an
cbv check (Case scruts anTel branches sr ann) = do
  scruts' <- mapM (cbv check) scruts
  
  -- logg $ "scruts"
  -- loggg $ lfullshow scruts
  -- logg $ scruts
  -- logg $ scruts'
  norm (cbv check) pure check $ Case scruts' anTel branches sr ann
cbv check (e@(Fun _ _)) = pure e -- TODO should probly still simplify for readability
cbv check (Pi aTy bodTy) = do
  aTy' <- (cbv check) aTy
  pure $ Pi aTy' bodTy -- TODO should probly still simplify for readability

cbv check e = norm (cbv check) pure check e



cbvCheck e = cbv checkcbv e

cbvDiffer :: (WithDynDefs m, Fresh m) => Term -> m Exp
cbvDiffer e = cbv differ e

checkcbv :: MonadError Err m => Exp -> Info -> Exp -> m Exp
checkcbv l info r | sameCon l r == Just False = do
  throwInfoError (show (e l) ++ "=!=" ++ show (e r)) info
  
-- this seems pretty hacky
checkcbv TyU info TyU = pure TyU
checkcbv (TConF tCNamel argsl _) obs (TConF tCNamer argsr _) 
  | tCNamel == tCNamer && length argsl == length argsr = do
      args <- mapM (\ (i, ll, rr) -> checkcbv ll (obsmap (Index i) obs) rr) $ zip3 [0..] argsl argsr
      pure $ TConF tCNamel args noAn

checkcbv (DConF dCNamel argsl _) obs (DConF dCNamer argsr _) 
  | dCNamel == dCNamer && length argsl == length argsr = do
      args <- mapM (\ (i, ll, rr) -> checkcbv ll (obsmap (Index i) obs) rr) $ zip3 [0..] argsl argsr
      pure $ DConF dCNamel args noAn

checkcbv (under -> Just l) obs r = checkcbv l obs r
checkcbv l obs (under -> Just r) = checkcbv l obs r
checkcbv l info r = pure $ Same l info r

differ TyU info TyU = pure TyU
differ (TConF tCNamel argsl _) obs (TConF tCNamer argsr _) 
  | tCNamel == tCNamer && length argsl == length argsr = do
      args <- mapM (\ (i, ll, rr) -> differ ll (obsmap (Index i) obs) rr) $ zip3 [0..] argsl argsr
      pure $ TConF tCNamel args noAn

differ (DConF dCNamel argsl _) obs (DConF dCNamer argsr _) 
  | dCNamel == dCNamer && length argsl == length argsr = do
      args <- mapM (\ (i, ll, rr) -> differ ll (obsmap (Index i) obs) rr) $ zip3 [0..] argsl argsr
      pure $ DConF dCNamel args noAn

differ (under -> Just l) obs r = differ l obs r
differ l obs (under -> Just r) = differ l obs r
differ l obs r = do
  l' <- normClean l
  r' <- normClean r
  pure $ Same l' obs r' -- a hacky mess
-- differ l obs r = pure $ Same l obs r 

-- check :: MonadError Err m => Exp -> Info -> Exp -> m Exp
-- check l info r | sameCon l r == Just False = do
--   throwInfoError (show (e l) ++ "=!=" ++ show (e r)) info
-- check l info r = pure $ Same l info r

noCheck l info r = pure $ Same l info r



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
