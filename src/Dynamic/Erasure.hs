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


module Dynamic.Erasure where

import Data.Set (Set)
import qualified Data.Set as Set

import Dynamic.Ast as C
-- import Erasure
import Ast
import UnboundHelper
import Unbound.Generics.LocallyNameless.Bind

import Unbound.Generics.LocallyNameless
import Helper
import Control.Monad
import GHC.Stack (HasCallStack)
import Control.Exception (assert)




erase :: HasCallStack =>
  Fresh m => C.Term -> m Ast.Term
erase (C.V x) = pure $ Ast.V $ rename x
erase (C.Ref x) = pure $ Ast.Ref x
erase (C.Fun bndBod) = do
  ((rename -> f, rename -> a), bod) <- unbind bndBod
  bod' <- erase bod
  pure $ Ast.Fun $ bind (f,a) bod' 
erase (C.App f a) = do
  f' <- erase f
  a' <- erase a
  pure $ Ast.App f' a'
erase (C.Pi aTy bndBodTy) = do
  aTy' <- erase aTy
  (rename -> a, bod) <- unbind bndBodTy
  bod' <- erase bod
  pure $ Ast.Pi aTy' $ bind a bod' 
erase (C.TConF tCName args _ _ ) = do
  args' <- mapM erase args
  pure $ apps (TCon tCName) args'
erase (C.DConF dCName args _ _ _) = do
  args' <- mapM erase args
  pure $ apps (DCon dCName) args'
erase (C.Case scruts branch _ ) = do
  scruts' <- mapM erase scruts
  branch' <- forM branch $ \ (C.Match bndbod) -> do
    (pats, bod) <- unbind bndbod 
    pats' <- mapM erasePat pats
    bod' <- erase bod
    pure $ Ast.Match $ bind pats' bod' -- it is possible for this to leak path vars
  pure $ Ast.Case scruts' noAn branch'
erase C.TyU = pure Ast.TyU
erase (C.C u _) = erase u
erase (C.Same u _ _ _) = erase u -- left biased
erase (C.Union (Set.toList -> (u:_)) _ ) = erase u -- left biased
erase e = pure $ Ast.Solve noAn -- error $ "unhandled " ++ show e 


erasePat :: Fresh m => C.Pat -> m Ast.Pat
erasePat (C.PVar x) = pure $ Ast.PVar $ rename x
erasePat (C.Pat dCName args _) = Ast.Pat dCName <$> mapM erasePat args




-- instance Er C.Var where
--   erase x = Ast.V $ rename x

-- instance Er C.Exp where
--   erase (C.V x) = Ast.V $ rename x
--   erase (C.Ref refName) = Ast.Ref refName
--   erase (C.Fun (B (self, x) bod)) = Ast.Fun $ B (rename self, rename x) $ erase bod
--   erase (f `C.App` a) = erase f `Ast.App` erase a
--   erase (C.Pi a (B x bod)) = Ast.Pi (erase a) $ B (rename x) $ erase bod
--   erase (C.TConF tCName inds _ _) = Ast.TConF tCName `apps` erase <$> inds
--   erase (C.DConF dCName args _ _ _) = Ast.DConF dCName `apps` erase <$> args
--   erase (C.Case scruts pats _) = Ast.Case (erase <$> scruts) ()




  -- erase (f `App` a) = erase f `App` erase a
  -- erase (Case scruts _ branches) = Case (erase <$> scruts) noAn $ fmap (\ (Match (B p b)) -> Match (B p $ erase b)) branches
  -- erase (Pos _ e _) = erase e
  -- erase e = e