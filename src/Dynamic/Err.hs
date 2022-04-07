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


module Dynamic.Err where

import Control.Applicative (Applicative (..), (<$>))
import Control.Monad (guard)
import Data.List (find)


import Data.Map (Map)
import qualified Data.Map as Map

import Data.Set (Set)
import qualified Data.Set as Set

import Data.Typeable (Typeable)
import GHC.Generics (Generic)

import SourcePos
import AlphaShow
import Unbound.Generics.LocallyNameless


-- TODO include info
data Err = Msg String (Maybe SourceRange)
  deriving (
  Show, 
  Generic, Typeable)

-- dumb stuff for debugging
instance Alpha Err
instance AlphaLShow Err

prettyErr :: Err -> String
prettyErr (Msg msg Nothing) = msg
prettyErr (Msg msg (Just range)) = unlines $ lines msg ++ prettyRange range
