{-# LANGUAGE GeneralizedNewtypeDeriving #-}
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


module Dynamic.Erase where
import Control.Applicative (Applicative (..), (<$>))
import Control.Monad (guard)
import Data.List (find)


import Data.Map (Map)
import qualified Data.Map as Map

import Data.Set (Set)
import qualified Data.Set as Set

import Data.Monoid (Any (..))
import Data.Typeable (Typeable)
import GHC.Generics (Generic)
import Unbound.Generics.LocallyNameless
import Control.Monad.Except
import Unbound.Generics.LocallyNameless.Unsafe (unsafeUnbind)
import UnboundHelper
import Helper

import qualified Dynamic.Ast as C

import Ast


eraseV :: C.Var -> Var
eraseV v = s2n $ name2String v

e :: C.Term -> Term
e = runFreshM . erase

-- TODo typeclass?
eraseCast :: Fresh m => C.Exp -> m C.Exp
eraseCast (C.V x _) = pure $ C.V x noAn
eraseCast (C.Fun bndBod _) = do
  ((f, a), bod) <- unbind bndBod
  bod' <- eraseCast bod
  pure $ C.Fun (bind (f,a) bod') noAn
eraseCast (C.App f a _) = do
  f' <- eraseCast f
  a' <- eraseCast a
  pure $ C.App f' a' noAn
eraseCast (C.Pi aTy bndBodTy) = do
  aTy' <- eraseCast aTy
  (a, bod) <- unbind bndBodTy
  bod' <- eraseCast bod
  pure $ C.Pi aTy' $ bind a bod'
eraseCast (C.TConF tCName args _) = do
  args' <- mapM eraseCast args
  pure $ C.TConF tCName args' noAn
eraseCast (C.DConF dCName args _ ) = do
  args' <- mapM eraseCast args
  pure $ C.DConF dCName args' noAn
eraseCast (C.Case scruts _ branch sr _) = do
  scruts' <- mapM eraseCast scruts
  branch' <- forM branch $ \ (C.Match bndbod) -> do
    (pats, (assigns, right -> bod)) <- unbind bndbod 
    -- pats' <- mapM erasePat pats
    bod' <- eraseCast bod
    pure $ C.Match $ bind pats (assigns, Right bod')
  pure $ C.Case scruts' noAn branch' sr noAn
eraseCast C.TyU = pure C.TyU
eraseCast (C.under -> Just u) = eraseCast u
eraseCast e = error $ "not doen yet, " ++ show e 

right (Right r) = r

erase :: Fresh m => C.Term -> m Term
erase (C.V x _) = pure $ V $ eraseV x
erase (C.Fun bndBod _) = do
  ((eraseV -> f, eraseV -> a), bod) <- unbind bndBod
  bod' <- erase bod
  pure $ Fun $ bind (f,a) bod' 
erase (C.App f a _) = do
  f' <- erase f
  a' <- erase a
  pure $ App f' a'
erase (C.Pi aTy bndBodTy) = do
  aTy' <- erase aTy
  (eraseV -> a, bod) <- unbind bndBodTy
  bod' <- erase bod
  pure $ Pi aTy' $ bind a bod' 
erase (C.TConF tCName args _) = do
  args' <- mapM erase args
  pure $ apps (TCon tCName) args'
erase (C.DConF dCName args _ ) = do
  args' <- mapM erase args
  pure $ apps (DCon dCName) args'
erase (C.Case scruts _ branch _ _) = do
  scruts' <- mapM erase scruts
  branch' <- forM branch $ \ (C.Match bndbod) -> do
    (pats, (_, right -> bod)) <- unbind bndbod 
    pats' <- mapM erasePat pats
    bod' <- erase bod
    pure $ Match $ bind pats' bod'
  pure $ Case scruts' noAn branch'
erase C.TyU = pure TyU
erase (C.under -> Just u) = erase u
erase e = error $ "unhandled " ++ show e 


erasePat :: Fresh m => C.Pat -> m Pat
erasePat (C.PVar x) = pure $ PVar $ eraseV x
erasePat (C.Pat _ dCName args) = Pat dCName <$> mapM erasePat args