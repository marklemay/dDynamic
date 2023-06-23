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

module Dynamic.Visitor where
-- TODO this is the kind of thing that should be generatable automatically

import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless.Internal.Fold (foldMapOf, toListOf)
import Unbound.Generics.LocallyNameless.Unsafe (unsafeUnbind)
import Dynamic.Ast

import Unbound.Generics.LocallyNameless.Unsafe (unsafeUnbind)
import Control.Monad.Writer
import Control.Monad.Identity
import Dynamic.Norm
import UnboundHelper
import SourcePos
import Dynamic.Eq
import PreludeHelper
import Dynamic.ElabBase
import Control.Monad (forM)


-- partially instantiate the visitor pattern for now

data VisitorM m a = VisitorM {
  -- first parameter allows for short cuircuting the remianing computations, or inspecting "unofficial"  parts of the expression
  vV :: Exp -> ((Var -> m a) -> m a) -> m a,
  vRef :: Exp -> ((RefName -> m a) -> m a) -> m a, 
  vFun :: Exp -> ((Var -> Var -> a -> m a)-> m a)-> m a,
  vApp :: Exp -> ((a -> a -> m a)-> m a) -> m a,
  vPi :: Exp -> ((a -> Var -> a -> m a) -> m a) -> m a,
  vTConF :: Exp -> ((TCName -> [a] -> (Tel Exp Ty ()) -> (Tel Exp Ty ()) -> m a) -> m a) -> m a, -- tell not counted
  vDConF :: Exp -> ((DCName -> [a] -> TCName -> Tel Exp Ty [Term] -> Tel Exp Ty () -> (Tel Exp Ty ())-> m a) -> m a) -> m a,
  vCase :: Exp -> (([a] -> [([Pat], a)] -> (An ([[Pat]], Maybe SourceRange)) -> m a) -> m a) -> m a, 
  vTyU :: Exp -> (m a -> m a) -> m a, 
  vC :: Exp -> ((a -> a -> m a) -> m a) -> m a, 
  vBlame :: Exp -> ((a -> a -> m a) -> m a) -> m a, 
  vSame :: Exp -> ((a -> Info -> a -> a -> m a) -> m a) -> m a,
  vUnion :: Exp -> ((a -> a -> a-> m a) -> m a) -> m a,
  vTind :: Exp -> ((Integer -> a ->  m a) -> m a) -> m a, 
  vDind :: Exp -> ((Integer -> a ->  m a) -> m a) -> m a
}


visitFresh :: (Fresh m) => VisitorM m a -> Exp -> m a
visitFresh v@(VisitorM{vV=vV}) e@(V x) = 
  vV e $ \ finish -> finish x
visitFresh v@(VisitorM{vRef=vRef}) e@(Ref x) = 
  vRef e $ \ finish -> finish x
visitFresh v@(VisitorM{vFun=vFun}) e@(Fun bndBod) =
  vFun e $ \ finish -> do
    ((s,x),bod) <- unbind bndBod
    bod' <- visitFresh v bod
    finish s x bod'
visitFresh v@(VisitorM{vApp=vApp}) e@(f `App` a) =
  vApp e $ \ finish -> do
    f' <- visitFresh v f
    a' <- visitFresh v a
    finish f' a'
visitFresh v@(VisitorM{vPi=vPi}) e@(Pi a bndBod) =
  vPi e $ \ finish -> do
    (x,bod) <- unbind bndBod
    a' <- visitFresh v a
    bod' <- visitFresh v bod
    finish a' x bod'
visitFresh v@(VisitorM{vTConF=vTConF}) e@(TConF name inds tel1 tel2) =
  vTConF e $ \ finish -> do
    inds' <- forM inds $ visitFresh v
    finish name inds' tel1 tel2
visitFresh v@(VisitorM{vDConF=vDConF}) e@(DConF name args (tcname,tel1) tel2 tel3) =
  vDConF e $ \ finish -> do
    args' <- forM args $ visitFresh v
    finish name args' tcname tel1 tel2 tel3
visitFresh v@(VisitorM{vCase=vCase}) e@(Case scruts branchs an) =
  vCase e $ \ finish -> do
    scruts' <- forM scruts $ visitFresh v
    branchs' <- forM branchs $ \ (Match bndBranch) -> do
      (pat, bod)<- unbind bndBranch
      bod' <-visitFresh v bod
      pure (pat, bod') 
    finish scruts' branchs' an
visitFresh v@(VisitorM{vTyU=vTyU}) e@TyU =
  vTyU e $ \ finish -> finish
visitFresh v@(VisitorM{vC=vC}) e@(C trm ty) = 
  vC e $ \ finish -> do
    trm' <- visitFresh v trm
    ty' <- visitFresh v ty
    finish trm' ty'
visitFresh v@(VisitorM{vBlame=vBlame}) e@(Blame trm ty) = 
  vBlame e $ \ finish -> do
    trm' <- visitFresh v trm
    ty' <- visitFresh v ty
    finish trm' ty'
visitFresh v@(VisitorM{vSame=vSame}) e@(Same l info ev r) = 
  vSame e $ \ finish -> do
    l' <- visitFresh v l
    ev' <- visitFresh v ev
    r' <- visitFresh v r
    finish l' info ev' r'
visitFresh v@(VisitorM{vUnion=vUnion}) e@(Union l ev r) = 
  vUnion e $ \ finish -> do
    l' <- visitFresh v l
    ev' <- visitFresh v ev
    r' <- visitFresh v r
    finish l' ev' r'
visitFresh v@(VisitorM{vTind=vTind}) e@(Tind i ev) = 
  vTind e $ \ finish -> do
    ev' <- visitFresh v ev
    finish i ev'
visitFresh v@(VisitorM{vDind=vDind}) e@(Dind i ev) = 
  vDind e $ \ finish -> do
    ev' <- visitFresh v ev
    finish i ev'

visitorSelf :: (Monad m) => VisitorM m Exp
visitorSelf = VisitorM {
  vV = \ _ finish -> finish $ \ x -> pure $ V x,
  vRef = \ _ finish -> finish $ \ x -> pure $ Ref x,
  vFun = \ _ finish -> finish $ \ s x bod -> pure $ Fun $ bind (s,x) bod,
  vApp = \ _ finish -> finish $ \ f a -> pure $ f `App` a,
  vPi = \ _ finish -> finish $ \ a x bod -> pure $ Pi a $ bind x bod,
  vTConF = \ _ finish -> finish $ \ name inds tel1 tel2 -> pure $ TConF name inds tel1 tel2,
  vDConF = \ _ finish -> finish $ \ name args tcname tel1 tel2 tel3 -> pure $ DConF name args (tcname, tel1) tel2 tel3,
  vCase = \ _ finish -> finish $ \ scruts branches an -> pure $ Case scruts (fmap (\ (p,b)-> Match $ bind p b) branches) an,
  vTyU = \ _ finish -> finish $ pure TyU,
  vC = \ _ finish -> finish $ \ trm ty -> pure $ C trm ty,
  vBlame = \ _ finish -> finish $ \ trm ty -> pure $ Blame trm ty,
  vSame = \ _ finish -> finish $ \ l info ev r -> pure $ Same l info ev r,
  vUnion = \ _ finish -> finish $ \ l ev r -> pure $ Union l ev r,
  vTind = \ _ finish -> finish $ \ i ev -> pure $ Tind i ev,
  vDind = \ _ finish -> finish $ \ i ev -> pure $ Dind i ev
}
-- ok this should be gen tested
