module Main where

import System.Environment
import Test.Tasty (defaultMain, testGroup, TestTree)

import Test.Tasty.HUnit (assertEqual, assertBool, testCase)
import StdLibTest
import Presentation.Surface
import Presentation.Cast
import Presentation.CastUncleaned
import Parser.Fun
import Parser.Exp
import Elab.Fun

-- import Dynamic.Main

main = --was the taty quickcheck timeout ever fixed?
  do 
      -- setEnv "TASTY_TIMEOUT" "12s" 
      setEnv "TASTY_TIMEOUT" "120s"
      -- setEnv "TASTY_TIMEOUT" "3600s"


      setEnv "TASTY_QUICKCHECK_TESTS" "10000"
      setEnv "TASTY_QUICKCHECK_MAX_SIZE" "500"
      -- setEnv "TASTY_QUICKCHECK_TESTS" "100000"
      -- setEnv "TASTY_QUICKCHECK_MAX_SIZE" "5000"
      -- setEnv "TASTY_QUICKCHECK_TESTS" "10000000"
      -- setEnv "TASTY_QUICKCHECK_MAX_SIZE" "500000"
      -- setEnv "TASTY_QUICKCHECK_TESTS" "100000000"
      -- setEnv "TASTY_QUICKCHECK_MAX_SIZE" "5000000"
      defaultMain allTests
      unsetEnv "TASTY_TIMEOUT"
      unsetEnv "TASTY_QUICKCHECK_TESTS"
      unsetEnv "TASTY_QUICKCHECK_MAX_SIZE"

allTests =
  testGroup
    "allTests"
    [
      -- operations we might want to show off live
      -- Presentation.Surface.tests,
      Presentation.Cast.tests,
      Presentation.CastUncleaned.tests,
      -- stdLibTest,
     Parser.Fun.tests
    --  ,
    --  Parser.Exp.tests,
    
    --  Elab.Fun.tests
    ]

