

{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DeriveDataTypeable, DeriveGeneric, MultiParamTypeClasses, FlexibleContexts, FlexibleInstances, DeriveFunctor, RankNTypes, LambdaCase  #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module Dynamic.PatternGenBool where

import Data.Map (Map)
import qualified Data.Map as Map

import Data.Set (Set)
import qualified Data.Set as Set

import Test.Tasty
import Unbound.Generics.LocallyNameless
import Data.Typeable (Typeable)
import GHC.Generics (Generic)

import Test.QuickCheck hiding (Fun)
import Test.Tasty.QuickCheck (testProperty)

import Test.Tasty.HUnit (Assertion(..), assertEqual, assertBool, testCase)

import Unbound.Generics.LocallyNameless.Unsafe (unsafeUnbind)
import Dynamic.Ast
import UnboundHelper
import Helper
import Env

-- import TestHelper
import ParserMonad
import SourcePos
import Parser
import Prelude hiding((^^), exp, pi)

import Unbound.Generics.LocallyNameless
import Control.Monad.Trans.Class


-- TODO in TestHelper
-- right' :: (HasCallStack) => Either [String] b -> IO b
-- right' (Left x) = counterexample (unlines x) True
-- right' (Right x) = pure x















-- since apparently their is no popular GenT Lib.. do some stupid hacks for now


px = s2n "px"
wild = s2n "_"


newtype BoolPat = BoolPat Pat

instance Arbitrary BoolPat where
  arbitrary = BoolPat <$> elements [Pat "t" [] px, Pat "f" [] px, PVar wild]

  shrink (BoolPat (PVar _)) = BoolPat <$> [Pat "t" [] px, Pat "f" [] px] -- or perhaps wild is simplest
  shrink (BoolPat (Pat "f" [] _)) = BoolPat <$> [Pat "t" [] px]
  shrink _ = []

newtype BoolPats = BoolPats [BoolPat]

-- instance Arbitrary BoolPat where
--   arbitrary = BoolPat <$> elements [Pat "t" [] px, Pat "f" [] px, PVar wild]

--   shrink (BoolPat (PVar _)) = BoolPat <$> [Pat "t" [] px, Pat "f" [] px] -- or perhaps wild is simplest
--   shrink (BoolPat (Pat "f" [] _)) = BoolPat <$> [Pat "t" [] px]
--   shrink _ = []


-- subtraction :: (Exp -> String) -> Exp -> Property
-- showParses sho e = 



-- arbitrarySizedBoolPat :: Int -> Gen Exp
-- arbitrarySizedBoolPat :: (Ord a, Num a) => a -> Gen Pat
-- arbitrarySizedBoolPat = elements ["t","f"]
-- arbitrarySizedExpr i = do 
--   var <- elements $ s2n <$> ["x","y","z"]
--   var2 <- elements $ s2n <$> ["x","y","z"]
--   rest <- arbitrarySizedExpr (i - 1)
--   e1 <- arbitrarySizedExpr ((i `div` 2) - 1)
--   e2 <- arbitrarySizedExpr (i `div` 2)

--   elements [
--    e1 ::: e2,
--    e1 `App` e2, Pi e1 $ bind var e2, Fun $ bind (var2, var) rest,
--     V var, TyU]
  
