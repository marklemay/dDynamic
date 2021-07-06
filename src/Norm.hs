{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ConstraintKinds, FlexibleContexts #-}

module Norm where
import GHC.Stack

import Unbound.Generics.LocallyNameless
import GHC.Generics (Generic)
import Data.Typeable (Typeable)

import Data.Map (Map)

import Data.Monoid (Any(..))
import Control.Applicative (Applicative(..), (<$>))
import Unbound.Generics.LocallyNameless.Internal.Fold (foldMapOf, toListOf)

import Debug.Trace
import Ast
import Helper
import UnboundHelper
import Env

import Control.Monad.Except (catchError, MonadError(throwError))
import Control.Monad (guard) -- TODO: need a version with string error
import Control.Monad.Reader


-- TODO use unsafeunbind to remove the fresh constraint if possible 

-- TODO this paremeterized norm can emulate the paremetric one?

-- | the defualt norm behavour, will always terminate with pure args, by "defualt" stops evaluation at WHNF
norm :: HasCallStack => (Fresh m, MonadError String m)
  => Exp -> (Exp -> m Exp) -> (Exp -> m Exp) -> m Exp
norm (V x) critN argN = pure $ V x
  -- TODO: safely evaluate the annotation?
norm (tm ::: ty) critN argN = critN tm

norm (f `App` arg) critN argN = do
  f' <- critN f
  arg' <- argN arg
  case f' of
    Fun bndbndbod -> do
      ((funName, aName), bod) <- unbind bndbndbod
      if not $ funName `occursIn` bod
        then critN $ subst aName arg' bod
        else pure $ f' `App` arg'
    _ -> pure $ f' `App` arg'
norm (Fun bndBod) critN argN = do
  ((self, arg), bod) <- unbind bndBod
  bod' <- argN bod
  pure $ Fun $ bind (self, arg) bod'
  -- TODO: safely evaluate the annotation?

norm (DCon dCName) critN argN = pure $ DCon dCName
norm (Case scrutinee ann branches) critN argN = do
  scrutinee' <-  critN scrutinee
  case asNeu scrutinee' of 
    Just (DCon cname, args) ->
      case lookup cname $ fmap (\ (Match name bndBod) -> (name, bndBod)) branches of
        Just bndBod -> do 
          (vs, bod) <- unbind bndBod
          guardThrow (length vs == length args) "not the same len" $ critN $ substs (zip vs args) bod
        Nothing -> throwError "constructor given was not matched"
    _ -> Case scrutinee' ann <$> mapM (\ (Match name bndBod) -> do (vs, bod) <- unbind bndBod; bod' <- argN bod; pure $ Match name $ bind vs bod') branches

norm (Pi aTy bnd) critN argN = do
  (argName, bod) <- unbind bnd
  bod' <- argN bod
  Pi <$> argN aTy <*> pure (bind argName bod') -- TODO: applicative helper?
norm (TCon tCName) critN argN = pure $ TCon tCName
-- norm (TCon tCName args) critN argN = TCon tCName <$> mapM argN args

norm (Solve target) critN argN = pure $ Solve target -- by defualt do not evaluate Solve
norm TyU critN argN = pure TyU
norm (Pos _ e _) critN argN = critN e

-- unsafe
whnf' :: (MonadError String m, DefnCtx ctx, MonadReader ctx m, Fresh m)
  => (Exp -> m Exp) -> Exp -> m Exp
whnf' argN (V x) = do
  {do (trm,_) <- lookupDef x; whnf' argN trm } `catchError` \ _ -> pure $ V x
  -- TODO: safely evaluate the annotation?
whnf' argN (f `App` arg) =  do
  f' <- whnf' pure f
  case f' of
    Fun bndbndbod -> do
      ((funName, aName), bod) <- unbind bndbndbod
      whnf' argN $ subst funName f' $ subst aName arg bod
      -- Pi forall makes sense to add definitions, so evaluation will be lazily momoized
    _ -> App <$> argN f' <*> argN arg
whnf' argN e = norm e (whnf' argN) argN

-- unsafe
whnf :: (MonadError String m, DefnCtx ctx, MonadReader ctx m, Fresh m)
  => Exp -> m Exp
whnf = whnf' pure


safeWhnf :: (Fresh m, MonadError String m)
  => Exp -> m Exp
safeWhnf e = norm e safeWhnf pure


-- isVal :: (DefnCtx ctx, MonadReader ctx m, Fresh m) => Exp -> m Bool
isVal :: (MonadReader ctx m, DefnCtx ctx, MonadError String m) => Exp -> m Bool
isVal (Fun _) = pure True
isVal (asNeu -> (Just (DCon _, args)) ) = allM isVal args
isVal (asNeu -> (Just (TCon _, args)) ) = allM isVal args
isVal (Solve _) = pure False -- throwprettyError "not handling ? for value yet"
isVal (Pi _ _) = pure True
isVal TyU = pure True

isVal (u ::: _) = isVal u
isVal (Pos _ u _) = isVal u

isVal (V x) = do
  mdef <- lookupDef' x 
  case mdef of
    Just (def,_) -> isVal def --questionable?
    Nothing -> pure False -- bald vars are not vals
isVal _ = pure False 

cbv :: (MonadReader ctx m, DefnCtx ctx, MonadError String m, Fresh m) => Exp -> m Exp
cbv (V x) = do (trm,_) <- lookupDef x; cbv trm
cbv (f `App` a) = do
  -- logg $ show f ++ "App" ++ show a
  f' <- cbv f
  a' <- cbv a
  av <- isVal a'
  case f' of
    Fun bndbndbod | av -> do -- TODO the better defualt?
      ((funName, aName), bod) <- unbind bndbndbod
      cbv $ subst funName f' $ subst aName a' bod
    _ -> pure $ f' `App` a'
cbv e = -- do logg $ "push to norm, " ++ codeshow e; 
  norm e cbv pure
-- TODO need to test thsi against std lib!


-- TODO: this is pretty wrong
-- TODO: don't eval under binder
eval :: (MonadError String m, DefnCtx ctx, MonadReader ctx m, Fresh m)
  => Exp -> m Exp
eval = whnf' eval

-- can still nonterminate on top level gerneral recursion
safeEval :: (MonadError String m, DefnCtx ctx, MonadReader ctx m, Fresh m)
  => Exp -> m Exp
safeEval e@(Fun _) = safeWhnf e
safeEval e = whnf' safeEval e



-- no bug, good test
-- esafewhnf = vflde $ safeWhnf $ (lam  (s2n "_") $ n 0) `App`  V (s2n "x") 