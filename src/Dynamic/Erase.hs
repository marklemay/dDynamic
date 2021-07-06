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
eraseV v = s2n $ name2String v -- TODO should probly be fresh under monad...

e :: C.Term -> Term
e = runFreshM . erase



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
erase (C.Case scrut motive branch _) = do
  scrut' <- erase scrut
  ((eraseV -> a, fmap eraseV -> params), outTy) <- unbind motive
  branch' <- forM branch $ \ (C.Match dCName bndbod) -> do
    (fmap eraseV -> args, bod) <- unbind bndbod 
    bod' <- erase bod
    pure $ Match dCName $ bind args bod'
  pure $ Case scrut' noAn branch'
erase C.TyU = pure TyU
erase (C.C u _ _ _) = erase u
erase e = error $ "unhandled " ++ show e 