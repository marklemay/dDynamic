module Presentation.Surface (tests) where

import Prelude hiding (head,exp)

import Test.Tasty (testGroup)
import Test.Tasty.HUnit 
import Test.Tasty.QuickCheck (testProperty)


import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless.Name
import Unbound.Generics.LocallyNameless.Bind
import GHC.Generics (Generic)
import Data.Typeable (Typeable)

import Data.Map (Map)
import qualified Data.Map as Map

import Ast
import Helper
import UnboundHelper
import Env
import Norm
import Eq
import Ty

import StdLib
import Control.Monad.Except (MonadError)

import Data.Either


import Repl
import Ast
import Parser
import ParserMonad

-- TODO present the parsing error better

-- TODO expected goes on teh right of @?=

file1 = "ex/a.dt"
file2 = "ex/b.dt"
file3 = "ex/c.dt"


tests = testGroup "Surface Language example works as expected"
  [ testCase "add" $ do
    Ok (ddefs,trmdefs) <- loadSurfaceFile file1
    let modul = TyEnv Map.empty ddefs trmdefs
    e <- parseIo exp "add 2 3"
    let e' = undermodule e ddefs
    (_,eTy) <- runTcMonadIo modul $ tyInfer e'

    expectedTy <- parseIo exp "Nat"
    let expectedTy' = undermodule expectedTy ddefs
    expectedTy' @?= eTy

    en <- runTcMonadIo modul $ cbv e'

    expecteden <- parseIo exp "5"
    let expecteden' = undermodule expecteden ddefs
    expecteden' @?= en,

  testCase "rep" $ do
    Ok (ddefs,trmdefs) <- loadSurfaceFile file1
    let modul = TyEnv Map.empty ddefs trmdefs
    e <- parseIo exp "rep Bool true 3"
    let e' = undermodule e ddefs
    (_,eTy) <- runTcMonadIo modul $ tyInfer e'

    expectedTy <- parseIo exp "Vec Bool 3"
    let expectedTy' = undermodule expectedTy ddefs
    expectedTy' @?= eTy

    en <- runTcMonadIo modul $ cbv e'

    expecteden <- parseIo exp "[true,true,true]<Bool>"
    let expecteden' = undermodule expecteden ddefs
    expecteden' @?= en,

  testCase "head" $ do
    Ok (ddefs,trmdefs) <- loadSurfaceFile file1
    let modul = TyEnv Map.empty ddefs trmdefs
    e <- parseIo exp "head Bool 2 [false,true,false]<Bool>" 
    let e' = undermodule e ddefs
    (_,eTy) <- runTcMonadIo modul $ tyInfer e'

    expectedTy <- parseIo exp "Bool"
    let expectedTy' = undermodule expectedTy ddefs
    expectedTy' @?= eTy

    en <- runTcMonadIo modul $ cbv e'

    expecteden <- parseIo exp "false"
    let expecteden' = undermodule expecteden ddefs
    expecteden' @?= en,

  testCase "append" $ do
    Ok (ddefs,trmdefs) <- loadSurfaceFile file1
    let modul = TyEnv Map.empty ddefs trmdefs
    e <- parseIo exp "append Nat 2 [1,2]<Nat> 3 [7,8,9]<Nat>" 
    let e' = undermodule e ddefs
    (_,eTy) <- runTcMonadIo modul $ tyInfer e'
    eTy' <- runTcMonadIo modul $ cbv eTy

    expectedTy <- parseIo exp "Vec Nat 5"
    let expectedTy' = undermodule expectedTy ddefs
    expectedTy' @?= eTy' --TODO all of these should be testing against equality directly!

    en <- runTcMonadIo modul $ cbv e'

    expecteden <- parseIo exp "[1,2,7,8,9]<Nat>"
    let expecteden' = undermodule expecteden ddefs
    expecteden' @?= en,


  testCase "okFun" $ do
    Ok (ddefs,trmdefs) <- loadSurfaceFile file1
    let modul = TyEnv Map.empty ddefs trmdefs
    e <- parseIo exp "okFun 3" 
    let e' = undermodule e ddefs
    (_,eTy) <- runTcMonadIo modul $ tyInfer e'

    expectedTy <- parseIo exp "Bool"
    let expectedTy' = undermodule expectedTy ddefs
    expectedTy' @?= eTy

    en <- runTcMonadIo modul $ cbv e'

    expecteden <- parseIo exp "true"
    let expecteden' = undermodule expecteden ddefs
    expecteden' @?= en,

  testCase (file2 ++ " gives 'good' error") $ do
    SurfaceTypeError e <- loadSurfaceFile file2
    assertBool "message contains carrot" $ elem '^' e,

  testCase (file3 ++ " gives 'good' error") $ do
    SurfaceTypeError e <- loadSurfaceFile file3
    assertBool "message contains carrot" $ elem '^' e
  ]
