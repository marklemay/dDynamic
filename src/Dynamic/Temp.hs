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


module Dynamic.Temp where

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
import Unbound.Generics.LocallyNameless.Alpha
import Unbound.Generics.LocallyNameless.Bind
import Unbound.Generics.LocallyNameless.Embed
import Unbound.Generics.LocallyNameless.Ignore
import Unbound.Generics.LocallyNameless.Internal.Fold (foldMapOf, toListOf)
import Unbound.Generics.LocallyNameless.Name
import Unbound.Generics.LocallyNameless.Rebind
import Unbound.Generics.LocallyNameless.Rec
import Unbound.Generics.LocallyNameless.Shift
import Unbound.Generics.LocallyNameless.Subst
import Control.Monad.Except
import Unbound.Generics.LocallyNameless.Unsafe (unsafeUnbind)

import Data.Foldable

import UnboundHelper
import AlphaShow

import Data.List hiding (scanl)

import Dynamic.Ast


--TODO consolodate with tyinf
apparentTy (tyInf -> (Just ty)) = ty
apparentTy e = error $ "no type read from " ++ show e


-- TODO this is likely tooo slow, for safty reasons need to do something like this
swapmotivevars :: Bind ([Var], Var) Ty -> Bind (Var, [Var]) Ty
swapmotivevars bnd = runFreshM $ do
  ((x,y), bod)<- unbind bnd
  pure $ bind (y, x) bod