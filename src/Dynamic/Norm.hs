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

import GHC.Stack


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

import PreludeHelper
import UnboundHelper

import Dynamic.Ast
import Dynamic.Env
import Dynamic.Err
import Dynamic.Erase



norm :: HasCallStack => (Fresh m, WithDynDefs m) => (Exp -> m Exp) -> (Exp -> m Exp) -> (Exp -> m Exp) -> Exp -> m Exp
norm crit whyN simp (V x ann) = do -- expand module deffinitions, TODO can facrtor this out like in the prevous attempt
   me <- getDefnm' x
   case me of
     Just e -> crit e
     Nothing -> pure $ V x ann
norm crit whyN simp (Same (C l _ _ _) info r) = crit $ Same l info r 
norm crit whyN simp (Same l info (C r _ _ _)) = crit $ Same l info r 
norm crit whyN simp (Same l info r) = do
  l' <- crit l
  r' <- crit r
  case (l',r') of
    (TyU, TyU) -> pure TyU
    (DCon dCName params _, DCon dCName' params' _)  | dCName == dCName' -> 
      error "depricated"
      -- do logg $ "depricated"  ;whyN $ DCon dCName (fmap (\(x, o', y) -> Same x ll o' y) (zip3 params (fmap (\ i -> Index i o) [0..]) params')) noAn
    (DConF dCName params _, DConF dCName' params' _)  | dCName == dCName' -> do
      resparams <- mapM whyN $ fmap (\(x, info', y) -> Same x info' y) (zip3 params (fmap (\ i -> obsmap (Index i) info) [0..]) params')
      resparams' <- mapM simp resparams
      -- logg $ "SAME FIRST!!!" ++ dCName
      pure $ DConF dCName resparams' noAn
    (tConPat -> Just (tCName, params), tConPat -> Just (tCName', params')) | tCName == tCName' -> do
      resparams <- mapM whyN $ fmap (\(x, info', y) -> Same x info'  y) (zip3 params (fmap (\ i -> obsmap (Index i) info) [0..]) params')
      resparams' <- mapM simp resparams
      pure $ tCon tCName resparams'
    (Fun bndbodl _, Fun bndbodr _) -> do
      ((selfl, argnamel), bodl) <- unbind bndbodl
      ((slefr, argnamer), bodr) <- unbind bndbodr
      -- logg ""
      -- logg bodl
      -- logg bodr
      let bod = Same bodl (obsmap (AppW (v argnamel)) info) $ subst slefr (v selfl) $ subst argnamer (v argnamel) bodr
      -- logg bod
      -- logg ""
      bod' <- whyN bod
      bod'' <- simp bod'
      pure $ Fun (bind (selfl, argnamel) bod'') noAn
    (Pi aTyl bndbodTyl, Pi aTyr bndbodTyr) -> do
      (argnamel, bodl) <- unbind bndbodTyl
      (argnamer, bodr) <- unbind bndbodTyr
      let aTy = Same aTyl (obsmap Aty info) aTyr
      let bodTy = Same bodl (obsmap (Bty (v argnamel)) info) $ subst argnamer (v argnamel) bodr

      aTy' <- whyN aTy
      bodTy' <- whyN bodTy

      aTy'' <- simp aTy'
      bodTy'' <- simp bodTy'

      pure $ Pi aTy'' $ bind argnamel bodTy'' -- TODO rename or swap would be better
    _ -> pure $ Same l' info r'

norm crit whyN simp (C trm uty why ty) = do
  uty' <- crit uty
  why' <- crit why 
  ty' <- crit ty
  case (uty', ty') of
    (TyU, TyU) -> crit trm -- TODO can be blocked by why' ?
    _ -> do 
      trm' <- simp trm
      pure $ C trm' uty' why' ty'

norm crit whyN simp (App f a an) = do
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
      pure $ TConF tCName args' $ ann $ substBind bndrestTel a -- TODO normalize annotation

    DConF dCName args (An Nothing) -> do
      args' <- mapM simp $ args ++ [a]
      pure $ DConF dCName args' noAn
    DConF dCName args (An (Just (tCName, TelBnd _ bndrestTel))) -> do -- assumes casts are already made
      args' <- mapM simp $ args ++ [a]
      pure $ DConF dCName args' $ ann (tCName, substBind bndrestTel a) -- TODO normalize annotation

    C u uty w t -> do
      case (uty, w, t) of

        (Pi aTy' bndbodTy', Pi aTyw bndbodTyw, Pi aTy bndbodTy) -> do
          -- logg "commute"
          let ac = C a aTy aTyw aTy' -- TODO swap the why?
          let underTy = substBind bndbodTy' ac
          let under = App u ac $ ann underTy
          crit $ C under underTy (substBind bndbodTyw a) (substBind bndbodTy a)
        (_, w, t) -> do
          w' <- whyN w
          u' <- simp u 
          uTy' <- simp uty 
          t' <- simp t 
          a' <- simp a
          -- an' <- mapM simp an
          logg "TODO simp ann" 
          pure $ App (C u' uTy' w' t') a' an -- TODO is it concievealbe that the entire cast is simplified out, but it didn't crtit out?

    _ -> do
      a' <- simp a
      -- an' <- mapM simp an
      logg "TODO simp ann" 
      pure $ App f' a' an


norm crit whyN simp (Case scrut bndmotive branches an) = do
  scrut' <- crit scrut
  case scrut' of
    DConF (flip lkUp branches -> (Just bndbod)) args (An Nothing) -> do
      bod <- substsBind' bndbod args 
      crit bod
    DConF (flip lkUp branches -> (Just bndbod)) args (An (Just (_, NoBnd _))) -> do -- block if the type annotation does not match
      bod <- substsBind' bndbod args 
      crit bod
    DConF (flip lkUp branches -> Nothing) _ _  -> error $ "mismatching constructor name" ++ show scrut'
    DConF _ _ _  -> error $ "misapplide scrutinee" ++ show scrut'
    
    C u uTy w t -> do
      -- logg $ "u, " ++ show u
      case (uTy, w, t) of -- TODO collapse case
        -- (Nothing, _, _) -> error "blocked by loss of type info in scrut" -- the question is why the some did not eat the cast

        (tConPat -> Just (tCname', args'), tConPat -> Just (tCnamew, argsw), tConPat -> Just (tCname, args)) 
          | tCname' == tCnamew && tCname == tCnamew -> do
            ((scrutName, argNames), motive) <- unbind bndmotive
            let outerBodTy = subst scrutName scrut' $ substs (zip argNames args) motive
            let innerBodTy = subst scrutName u $ substs (zip argNames args') motive
            let under = Case u bndmotive branches $ ann (tCname', innerBodTy)
            crit $ C under innerBodTy (subst scrutName scrut' $ substs (zip argNames argsw) motive) outerBodTy

        (tConPat -> Just (tCname', args'), tConPat -> Just (tCnamew, argsw), tConPat -> Just (tCname, args)) ->
          error $ "apparently impossible typecast in scrut, " ++ show scrut'

        _ -> do
          w' <- whyN w
          uTy' <- simp uTy
          u' <- simp u 
          t' <- simp t
          logg "TODO simp an, simp branches, simp motive" 
          pure $ Case (C u' uTy' w' t') bndmotive branches an

    _ -> do
      logg "TODO simp an, simp branches, simp motive" 
      pure $ Case scrut' bndmotive branches an


norm crit whyN simp (DConF dCName params an) = do
  params' <- mapM simp params
  logg "TODO simp ty ann" 
  pure $ DConF dCName params an
norm crit whyN simp (TConF dCName params an) = do
  params' <- mapM simp params
  logg "TODO simp ann" 
  pure $ TConF dCName params an
norm crit whyN simp (Pi aty bndBodTy) = do
  aty' <- simp aty
  (aName, bodTy) <- unbind bndBodTy
  bodTy' <- simp bodTy
  pure $ Pi aty' $ bind aName bodTy'
  
norm crit whyN simp (Fun bndBod ann) = do
  logg "TODO simp ann" 
  ((fname,aName), bod) <- unbind bndBod
  bod' <- simp bod
  pure $ Fun (bind (fname,aName) bod') ann


norm crit whyN simp TyU = pure TyU
norm crit whyN simp e = do logg $ "not done yet" ++ show e ; pure e


whnf :: (Fresh m, WithDynDefs m) => Exp -> m Exp
whnf = norm whnf pure pure


-- whnfty
whnfann :: (Fresh m, WithDynDefs m) => Exp -> m Exp
whnfann (C trm uty why ty) = do
  ty' <- whnf ty
  pure $ C trm uty why ty'
whnfann (App f a (An (Just ty))) = do
  ty' <- whnf  ty
  pure $ App f a (An (Just ty'))
whnfann (Case s m b (An (Just (tCName, ty)))) = do
  ty' <- whnf ty
  pure $ Case s m b (An (Just (tCName, ty')))
whnfann x = pure x -- everything else already in whnf



cbvCheck :: (MonadError Err m, Fresh m, WithDynDefs m) => Term -> m Exp
cbvCheck (Same l info r) | sameCon l r == Just False = do
  throwInfoError (show (e l) ++ "=/=" ++ show (e r)) info
  -- error "throw info error"
  -- runWithSourceLocMT (throwPrettyError $ "because " ++ show o ++ ", " ++ show (e l) ++ "=/=" ++ show (e r)) $ Just src
cbvCheck (App f a ann) = do
  f' <- cbvCheck f
  a' <- cbvCheck a
  -- TODO check that a is a value!
  norm cbvCheck cbvCheck pure $ App f' a' ann --TODO some redundant computation... but the definition is at least tight
cbvCheck (C u uTy w t) = do
  u' <- cbvCheck u
  norm cbvCheck cbvCheck pure $ C u' uTy w t
cbvCheck (TConF tCName args an) = do
  args' <- mapM cbvCheck args
  pure $ TConF tCName args an
cbvCheck (DConF dCName args an) = do
  args' <- mapM cbvCheck args
  pure $ DConF dCName args an
cbvCheck e = norm cbvCheck cbvCheck pure e



whnfCheck :: (Fresh m, MonadError Err m, WithDynDefs m) => Exp -> m Exp
whnfCheck (Same l info r) | sameCon l r == Just False = 
  throwInfoError (show (e l) ++ "=/=" ++ show (e r)) info
whnfCheck e = norm whnfCheck whnfCheck pure e


isCon :: Exp -> Bool
isCon TyU = True
isCon (Pi _ _) = True
isCon (Fun _ _) = True
isCon (tConPat -> Just _) = True
isCon (DCon _ _ _) = True
isCon (DConF _ _ _) = True --TODO: not exactly right
isCon _ = False

sameCon :: Exp -> Exp -> Maybe Bool
sameCon TyU TyU = Just True
sameCon (tConPat -> Just (s1, _)) (tConPat -> Just (s2, _)) | s1 == s2 = Just True
sameCon (DCon s1 _ _) (DCon s2 _ _) | s1 == s2 = Just True
sameCon (DConF s1 _ _) (DConF s2 _ _) | s1 == s2 = Just True
sameCon (Fun _ _) (Fun _ _) = Just True
sameCon (Pi _ _) (Pi _ _) = Just True
sameCon e1 e2 | isCon e1 && isCon e2 = Just False
sameCon _ _ = Nothing 
