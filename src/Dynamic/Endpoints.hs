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
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module Dynamic.Endpoints where

import Dynamic.Ast
import Unbound.Generics.LocallyNameless
import Dynamic.Norm
import Control.Monad.Except

import Data.Map (Map)
import qualified Data.Map as Map

import Data.Set (Set)
import qualified Data.Set as Set
import GHC.Stack (HasCallStack)
import UnboundHelper
import PreludeHelper
import Dynamic.ElabBase
import Dynamic.Env
import Control.Monad.State
import AlphaShow (lfullshow)
import Unbound.Generics.LocallyNameless.Unsafe (unsafeUnbind)


-- TODO make a visitor Map
endpoints :: Exp ->[Exp]

endpoints (Fun (unsafeUnbind -> ((f,x), bod))) = fmap (\ bod' -> Fun $ bind (f,x) bod' ) $ endpoints bod
-- endpoints (DConF dCName [Term] (TCName, Tel Exp Ty [Term])  -- running tel
--     (Tel Exp Ty ()) --full
--     (Tel Exp Ty ())) = fmap (\ bod' -> Fun $ bind (f,x) bod' ) $ endpoints bod
  -- Fun <$> bind (f,x) <*> endpoints bod
endpoints atom = [atom]
