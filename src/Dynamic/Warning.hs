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


module Dynamic.Warning where
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
import Dynamic.Visitor
import GHC.Generics
import Data.Data
import AlphaShow

data Warning 
  = EqWarning Exp -- left
    Info Exp -- evidence
    Exp --right
  | Unmatched [[Pat]] --non-empty
    (Maybe SourceRange)
    deriving (
  -- Show, 
  Generic, Typeable)
  -- just for debugging
instance Alpha Warning
instance AlphaLShow Warning
instance Show Warning where
  show = lfullshow


visitorWarnSame :: (MonadWriter [Warning] m, Fresh m) => VisitorM m  Exp
visitorWarnSame = visitorSelf {
  vSame = \_ finish -> finish $ \ l info ev r -> do

    -- tell [(l, r, info)]
    tell [EqWarning l info ev r]
    pure $ Same l info ev r
  ,
  vCase = \_ finish -> finish $ \ scruts branches unmatched -> do
    case unmatched of 
      An (Just (p@(_:_), sr)) -> tell [Unmatched p sr]
      _ -> pure ()
      
    pure $ Case scruts (fmap (\ (p,e)-> Match $ bind p e) branches) unmatched
}

visitorCleanSame :: (Fresh m) => VisitorM m  Exp
visitorCleanSame = visitorSelf {
  vSame = \_ finish -> finish $ \ l info ev r -> do

    -- loggg ""
    -- loggg ""
    -- loggg ""
    -- loggg ""
    -- logg "Clean "
    -- -- logg "l="
    -- -- logg l

    -- -- logg "!!"

    -- l' <- whnf l
    -- r' <- whnf r
    -- eq l' info ev r'
    eq l info ev r
}

visitorCleanSameDef :: (Fresh m, WithDynDefs m) => VisitorM m Exp
visitorCleanSameDef = visitorSelf {
  vSame = \_ finish -> finish $ \ l info ev r -> do
    eqDef l info ev r
}


-- eraseCast e = runIdentity $ runFreshMT $ visitFresh visitorSelf {
--   vC = \_ finish -> finish $ \ trm _ -> pure trm
-- } e

eraseCast' :: Fresh m => Term -> m Exp
eraseCast' e = visitFresh visitorSelf {
  vC = \ (C trm _) _ -> eraseCast' trm
} e

eraseCast :: Term -> Exp
eraseCast e = runIdentity $ runFreshMT $ eraseCast' e
-- runIdentity $ runFreshMT $ 

rwf :: Monoid w => FreshMT (WriterT w Identity) a -> (a, w)
rwf e = runIdentity $ runWriterT $ runFreshMT $ e

e0 = rwf $ visitFresh visitorWarnSame TyU
-- e1 = rwf $ visitFresh visitorWarnSame $ efun

-- e2 = rwf $ visitFresh visitorWarnSame $ Same TyU (Info Nothing []) TyU TyU 

-- e3 = rwf $ visitFresh visitorWarnSame $ Same TyU (Info Nothing []) TyU (Same (Same TyU (Info Nothing []) TyU TyU ) (Info Nothing []) TyU TyU ) 



-- efun = Fun $ bind (s2n "f",s2n "x") $ Same TyU (Info Nothing []) TyU (V $  s2n "x")