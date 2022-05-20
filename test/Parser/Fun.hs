{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DeriveDataTypeable, DeriveGeneric, MultiParamTypeClasses, FlexibleContexts, FlexibleInstances, DeriveFunctor, RankNTypes, LambdaCase  #-}

module Parser.Fun where



import Data.Map (Map)
import qualified Data.Map as Map

import Data.Set (Set)
import qualified Data.Set as Set

import Test.Tasty
import Unbound.Generics.LocallyNameless
import Data.Typeable (Typeable)
import GHC.Generics (Generic)

import Helper

import Test.QuickCheck hiding (Fun)
import Test.Tasty.QuickCheck (testProperty)

import Test.Tasty.HUnit (Assertion(..), assertEqual, assertBool, testCase)

import Unbound.Generics.LocallyNameless.Unsafe (unsafeUnbind)
import Ast
import UnboundHelper


import Parser.Common

-- import TestHelper
import ParserMonad
import SourcePos
import Parser
import Prelude hiding((^^), exp, pi)

import Debug.Trace

-- TODO in TestHelper
-- right' :: (HasCallStack) => Either [String] b -> IO b
-- right' (Left x) = counterexample (unlines x) True
-- right' (Right x) = pure x


-- TODO (HasCallStack) 
x =~= y = counterexample (show x ++ " not alpha equivalent to " ++ show y ++ 
    "\n" ++ codeshow x ++
    "\n" ++ codeshow y) (x == y)


showParses :: (Exp -> String) -> Exp -> Property
showParses sho e = 
  let se = sho e
      fakePath = ""
  in case prettyParse fakePath se exp of -- trace se $ 
    Left er -> counterexample (show er) False
    Right ee -> 
       counterexample (
       "did not parse valid position ranges. printed, " ++ se++
       "\n" ++ codeshow ee) (validPos' (SourcePos fakePath 0 0) (SourcePos fakePath 9999 9999) ee)
      .&&.
      counterexample (
       "printed, " ++ se++
       "\n" ++ show e ++ " not alpha equivalent to " ++ show ee ++ 
       "\n" ++ codeshow e ++
       "\n" ++ codeshow ee) (e == ee)
  -- ee <- right' $ prettyParse "" se exp
  
  



tests :: TestTree
tests =
  testGroup "parse the functional fragment"
     [testCase "type ascription right associative" $ do
         e <- parseIo exp "*:*:*"
         assertEqual "*:(*:*)" (TyU ::: (TyU ::: TyU)) e
      , testCase "app has higher prec then : " $ do
         e <- parseIo exp "*:* *"
         assertEqual "*:(* *)" (TyU ::: (TyU `App` TyU)) e
      , testProperty "simple fully paren" $ showParses (\e -> simpleShow True e 0)
      , testProperty "simple min-paren" $ showParses (\e -> simpleShow False e 0)
      , testProperty "pretty fully paren" $ showParses (\e -> prettyShow True e 0)
      , testProperty "pretty min-paren" $ showParses (\e -> prettyShow False e 0)
      -- , testProperty "show instance" $ showParses show -- Turn it on when we have good show
       ]






arbitrarySizedExpr :: Int -> Gen Exp
arbitrarySizedExpr i | i < 1 = do 
  var <- elements $ s2n <$> ["x","y","z"]
  elements [V var, TyU]
arbitrarySizedExpr i = do 
  var <- elements $ s2n <$> ["x","y","z"]
  var2 <- elements $ s2n <$> ["x","y","z"]
  rest <- arbitrarySizedExpr (i - 1)
  e1 <- arbitrarySizedExpr ((i `div` 2) - 1)
  e2 <- arbitrarySizedExpr (i `div` 2)

  elements [
   e1 ::: e2,
   e1 `App` e2, Pi e1 $ bind var e2, Fun $ bind (var2, var) rest,
    V var, TyU]
  

instance Arbitrary Exp where
  arbitrary = sized arbitrarySizedExpr

  shrink = fullShrink shrink (\_ -> [])

  -- shrink e = TyU : genericShrink e -- oh yeah generic shrink is broke?
-- instance  Arbitrary SourcePos where
--   arbitrary = undefined

--   shrink _ = []

-- instance  Arbitrary Match where
--   arbitrary = undefined

--   shrink _ = []



-- instance (Alpha p)=> Arbitrary (Bind p Term) where
--   arbitrary = undefined

--   shrink (unsafeUnbind-> (p, bod)) =
--    bind p <$> shrink bod


-- instance  Arbitrary Var where
--   arbitrary = elements $ s2n <$> ["x","y","z"]

--   shrink _ = []


-- instance (Arbitrary a) => Arbitrary (An a) where
--   arbitrary = undefined

--   shrink (An (Just a)) = An Nothing : [An (Just a') | a' <- shrink a]
--   shrink (An Nothing) = []


