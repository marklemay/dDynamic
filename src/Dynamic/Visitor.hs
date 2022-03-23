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
  vCase :: Exp -> (([a] -> [([Pat], a)] -> (An [([Pat], SourceRange)]) -> m a) -> m a) -> m a, 
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
visitFresh v e = undefined 

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
  vBlame = \ _ finish -> finish $ \ trm ty -> pure $ C trm ty,
  vSame = \ _ finish -> finish $ \ l info ev r -> pure $ Same l info ev r,
  vUnion = \ _ finish -> finish $ \ l ev r -> pure $ Union l ev r,
  vTind = \ _ finish -> finish $ \ i ev -> pure $ Tind i ev,
  vDind = \ _ finish -> finish $ \ i ev -> pure $ Dind i ev
}

visitorWarnSame :: (MonadWriter [(Exp, Exp, Info)] m, Fresh m) => VisitorM m  Exp
visitorWarnSame = visitorSelf {
  vSame = \_ finish -> finish $ \ l info ev r -> do
    l' <- whnf l -- TODO needs a safe eq
    r' <- whnf r
    if l' `aeq` r'
    then pure $ C l' ev
    else do
      tell [(l', r', info)]
      pure $ Same l' info ev r' 
}
rwf :: Monoid w => FreshMT (WriterT w Identity) a -> (a, w)
rwf e = runIdentity $ runWriterT $ runFreshMT $ e

e0 = rwf $ visitFresh visitorWarnSame TyU
e1 = rwf $ visitFresh visitorWarnSame $ efun

e2 = rwf $ visitFresh visitorWarnSame $ Same TyU (Info Nothing []) TyU TyU 

e3 = rwf $ visitFresh visitorWarnSame $ Same TyU (Info Nothing []) TyU (Same (Same TyU (Info Nothing []) TyU TyU ) (Info Nothing []) TyU TyU ) 



efun = Fun $ bind (s2n "f",s2n "x") $ Same TyU (Info Nothing []) TyU (V $  s2n "x")
--visitFresh visitorWarnSame 


-- TODO can generalize over binding strategy (for instance destructive visists may not need to care as much)
-- visit :: (Monad m) => VisitorM m a -> Exp -> m a
-- visit v@(VisitorM{vV=vV}) e@(V x) = 
--   vV e $ \ f -> f x
-- visit v@(VisitorM{vSame=vSame}) e@(Same l info ev r) = 
--   vSame e $ \ f -> do
--     l' <- visit v l
--     ev' <- visit v ev
--     r' <- visit v r
--     f l' info ev' r'
-- visit v e = undefined 


-- data VisitorM m a = VisitorM {
--   -- first parameter allows for short cuircuting the remianing computations, or inspecting "unofficial"  parts of the expression
--   vV :: Exp -> Var -> m a,
--   vFun :: Exp -> Var -> Var -> a -> m a,
--   vApp :: Exp -> a -> a -> m a,
--   vPi :: Exp -> (a -> Var -> a -> a) -> m a,
--   vTConF :: Exp -> (TCName -> [a] -> a) -> m a, -- tell
--   vDConF :: Exp -> (DCName -> [a] -> a) -> m a, -- tell
--   vRef :: Exp -> (RefName -> a) -> m a, 
--   vCase :: Exp -> ([a] -> [(Pat, a)]-> a) -> m a, 
--   vTyU :: Exp -> m a, 
--   vC :: Exp -> (a -> a -> a) -> m a, 
--   vBlame :: Exp -> (a -> a -> a) -> m a, 
--   vSame :: Exp -> (a -> Info -> a -> a) -> m a, 
--   vUnion :: Exp -> (a -> a -> a) -> m a, 
--   vTcon :: Exp -> (Integer -> a -> a) -> m a, 
--   vDcon :: Exp -> (Integer -> a -> a) -> m a
-- }

-- visit :: (Monad m) => VisitorM m a -> Exp -> m a
-- visit (VisitorM{vV=vV}) e@(V x) = vV e x
-- visit v@(VisitorM{vFun=vFun}) e@(Fun (unsafeUnbind -> ((selfName, argName), bod))) = do
--   bod' <- visit v bod
--   f' <- vFun e selfName argName bod'
--   pure f'
-- visit v@(VisitorM{vApp=vApp}) e@(f `App` a) = do
--   f' <- visit v f
--   a' <- visit v a
--   app <- vApp e f' a'
--   pure app
--   -- <*> visit v f <*> visit v a
-- visit v e = undefined 

-- visitorSelf :: (Applicative m) => VisitorM m Exp
-- visitorSelf = 
--   VisitorM {
--   vV = \ e x -> pure $ V x,
--   vFun = \ e self inp bod -> pure $ Fun $ bind (self, inp) bod,
--   vApp = \ e f a ->  pure $ f `App` a
--   -- vPi :: (a -> Var -> a -> a) -> m a,
--   -- vTConF :: (TCName -> [a] -> a) -> m a, -- tell
--   -- vDConF :: (DCName -> [a] -> a) -> m a, -- tell
--   -- vRef :: (RefName -> a) -> m a, 
--   -- vCase :: ([a] -> [(Pat, a)]-> a) -> m a, 
--   -- vTyU :: m a, 
--   -- vC :: (a -> a -> a) -> m a, 
--   -- vBlame :: (a -> a -> a) -> m a, 
--   -- vSame :: (a -> Info -> a -> a) -> m a, 
--   -- vUnion :: (a -> a -> a) -> m a, 
--   -- vTcon :: (Integer -> a -> a) -> m a, 
--   -- vDcon :: (Integer -> a -> a) -> m a
-- }


-- -- data Walker a = Walker {
-- --   wV :: Var -> a,
-- --   wFun :: ((Var, Var) -> a -> a) -> a,
-- --   wApp :: (a -> a -> a) -> a,
-- --   wPi :: (a -> Var -> a -> a) -> a,
-- --   wTConF :: (DCName -> [a] -> a) -> a, -- tell
-- -- }
-- -- data WalkerM m a = 