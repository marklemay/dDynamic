

module TestHelper where

import GHC.Stack
import Test.Tasty.HUnit


assertLeft :: (Show a1, HasCallStack) => Either a2 a1 -> IO ()
assertLeft (Right x) = assertFailure $ "Right " ++ show x
assertLeft (Left x) = pure ()

assertRight :: (Show a, HasCallStack) => Either a b -> IO ()
assertRight (Left x) = assertFailure $ "Left " ++ show x
assertRight (Right x) = pure ()



right :: (Show a, HasCallStack) => Either a b -> IO b
right (Left x) = assertFailure $ "Left " ++ show x
right (Right x) = pure x

