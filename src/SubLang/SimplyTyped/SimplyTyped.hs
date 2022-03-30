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


module SubLang.SimplyTyped.SimplyTyped where


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
import Unbound.Generics.LocallyNameless.Internal.Fold (foldMapOf, toListOf)
import Unbound.Generics.LocallyNameless.Unsafe (unsafeUnbind)

import UnboundHelper
import AlphaShow

type Var = Name Trm
data Trm
  = V Var
  | Lam Ty (Bind Var Trm)
  | App Trm Trm
  deriving
    ( Generic,
      Typeable
    )


instance Alpha Trm
instance Subst Trm Trm where
  -- `isvar` identifies the variable case in your AST.
  isvar (V x) = Just (SubstName x)
  isvar _     = Nothing
instance Eq Trm where
  (==) = aeq
  
instance AlphaLShow Trm
instance Show Trm where
  show = lfullshow

data Ty 
  = Atom String
  | Arrow Ty Ty
  deriving
    ( Generic,
      Typeable, Show, Eq
    )

instance Alpha Ty
instance Subst Trm Ty 
instance AlphaLShow Ty


type TyCtx = Map Var Ty

synth :: Integer -> TyCtx -> [(Trm,Ty)]
synth i ctx | i<=1 = do
  (v,ty') <- Map.toList ctx
  pure $ (V v,ty')
synth i ctx = do
  aTy <- synthAnyTy (i `div` 2)
  aTy <- synthAnyTy (i `div` 2)


-- synth :: Integer -> TyCtx -> Ty -> [Trm]
-- synth i ctx ty | i<=0 = do
--   (v,ty') <- Map.toList ctx
--   if ty' == ty
--   then pure $ V v
--   else []

synthInhabitableTy :: Integer -> TyCtx -> [Ty]
synthInhabitableTy i ctx | i<=0 = do
  (v,ty') <- Map.toList ctx
  pure ty'
-- synthInhabitableTy i ctx = do
--   aTy <- map Atom ["A".."D"] ++ synthInhabitableTy (i-1) ctx


synthAnyTy :: Integer -> [Ty]
synthAnyTy i | i<= 1= Atom <$> ["A","B","C","D"]
synthAnyTy i = do
  aTy <- synthAnyTy (i `div` 2)
  bodTy <- synthAnyTy (i `div` 2)
  pure $ aTy `Arrow` bodTy 

-- type Var a = Name (Ty a)

-- data Trm a
--   = V (Var a) -- (Ty a)
--   | Lam (Ty a) (Bind (Var a) (Trm a))
--   | App (Bind (Var a) (Ty a))

-- data Ty a
--   = Atom a
--   | Arrow (Ty a) (Ty a)


e = synth 0 (Map.fromList [(s2n "x", Atom "hi"),(s2n "y", Atom "bye"),(s2n "z", Atom "hi")]) (Atom "hi")