module Presentation.Cast where

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

import Helper
import UnboundHelper
import StdLib
import Control.Monad.Except (MonadError)

import Data.Either

import  Ast ()

import Repl
import  Dynamic.Ast 
import  Dynamic.Norm
import  Dynamic.Err
import  Dynamic.Elab
import  Dynamic.ElabModule
import  Dynamic.Env
import  Dynamic.Helper
import  Dynamic.Erase

import Parser
import ParserMonad

-- TODO present the parsing error better
file1 = "ex/a.dt"
file2 = "ex/b.dt"
file3 = "ex/c.dt"



tests = testGroup "Cast Language examples works as expected"
  [
    testGroup file1 [
      testCase "add" $ do
        Ok (ddefs,trmdefs) <- loadFile file1
        let modul = makeMod ddefs trmdefs
        e <- parseIo exp "add 2 3"
        let e' = undermodule e modul
        e'' <- runCIo modul $ elabInf e' Map.empty Map.empty []

        let Just eTy = tyInf e''

        expectedTy <- parseIo exp "Nat"
        let expectedTy' = undermodule expectedTy modul
        expectedTy'' <- runCIo modul $ elabInf expectedTy' Map.empty Map.empty []

        Dynamic.Erase.e eTy @?= Dynamic.Erase.e expectedTy''

        en <- runCIo modul $ cbvCheck e''

        expecteden <- parseIo exp "5"
        let expecteden' = undermodule expecteden modul
        expecteden'' <- runCIo modul $ elabInf expecteden' Map.empty Map.empty []

        Dynamic.Erase.e en @?= Dynamic.Erase.e expecteden''
        ,
      testCase "rep" $ do
        Ok (ddefs,trmdefs) <- loadFile file1
        let modul = makeMod ddefs trmdefs
        e <- parseIo exp "rep Bool true 3"
        let e' = undermodule e modul
        e'' <- runCIo modul $ elabInf e' Map.empty Map.empty []

        let Just eTy = tyInf e''

        expectedTy <- parseIo exp "Vec Bool 3"
        let expectedTy' = undermodule expectedTy modul
        expectedTy'' <- runCIo modul $ elabInf expectedTy' Map.empty Map.empty []

        Dynamic.Erase.e eTy @?= Dynamic.Erase.e expectedTy''

        en <- runCIo modul $ cbvCheck e''

        expecteden <- parseIo exp "[true,true,true]<Bool>"
        let expecteden' = undermodule expecteden modul
        expecteden'' <- runCIo modul $ elabInf expecteden' Map.empty Map.empty []

        Dynamic.Erase.e en @?= Dynamic.Erase.e expecteden''
        ,

      testCase "head" $ do
        Ok (ddefs,trmdefs) <- loadFile file1
        let modul = makeMod ddefs trmdefs
        e <- parseIo exp "head Bool 2 [false,true,false]<Bool>" 
        let e' = undermodule e modul
        e'' <- runCIo modul $ elabInf e' Map.empty Map.empty []

        let Just eTy = tyInf e''

        expectedTy <- parseIo exp "Bool"
        let expectedTy' = undermodule expectedTy modul
        expectedTy'' <- runCIo modul $ elabInf expectedTy' Map.empty Map.empty []

        Dynamic.Erase.e eTy @?= Dynamic.Erase.e expectedTy''

        en <- runCIo modul $ cbvCheck e''

        expecteden <- parseIo exp "false"
        let expecteden' = undermodule expecteden modul
        expecteden'' <- runCIo modul $ elabInf expecteden' Map.empty Map.empty []

        Dynamic.Erase.e en @?= Dynamic.Erase.e expecteden''
        ,

    --  testCase "append" $ do
    --     Ok (ddefs,trmdefs) <- loadFile file1
    --     let modul = makeMod ddefs trmdefs
    --     e <- parseIo exp "append Nat 2 [1,2]<Nat> 3 [7,8,9]<Nat>" 
    --     let e' = undermodule e modul
    --     e'' <- runCIo modul $ elabInf e' Map.empty Map.empty []

    --     let Just eTy = tyInf e''
    --     eTy' <- runCIo modul $ cbvCheck eTy

    --     expectedTy <- parseIo exp "Vec Nat 5"
    --     let expectedTy' = undermodule expectedTy modul
    --     expectedTy'' <- runCIo modul $ elabInf expectedTy' Map.empty Map.empty []

    --     Dynamic.Erase.e eTy' @?= Dynamic.Erase.e expectedTy'' --TODO more direct test of eqaality

    --     en <- runCIo modul $ cbvCheck e''

    --     expecteden <- parseIo exp "[1,2,7,8,9]<Nat>"
    --     let expecteden' = undermodule expecteden modul
    --     expecteden'' <- runCIo modul $ elabInf expecteden' Map.empty Map.empty []

    --     Dynamic.Erase.e en @?= Dynamic.Erase.e expecteden'',

     testCase "okFun" $ do
        Ok (ddefs,trmdefs) <- loadFile file1
        let modul = makeMod ddefs trmdefs
        e <- parseIo exp "okFun 3" 
        let e' = undermodule e modul
        e'' <- runCIo modul $ elabInf e' Map.empty Map.empty []

        let Just eTy = tyInf e''

        expectedTy <- parseIo exp "Bool"
        let expectedTy' = undermodule expectedTy modul
        expectedTy'' <- runCIo modul $ elabInf expectedTy' Map.empty Map.empty []

        Dynamic.Erase.e eTy @?= Dynamic.Erase.e expectedTy''

        en <- runCIo modul $ cbvCheck e''

        expecteden <- parseIo exp "true"
        let expecteden' = undermodule expecteden modul
        expecteden'' <- runCIo modul $ elabInf expecteden' Map.empty Map.empty []

        Dynamic.Erase.e en @?= Dynamic.Erase.e expecteden''
      ],
    testGroup file2 [
      testCase "add" $ do
        Ok (ddefs,trmdefs) <- loadFile file2
        let modul = makeMod ddefs trmdefs
        e <- parseIo exp "add 2 3"
        let e' = undermodule e modul
        e'' <- runCIo modul $ elabInf e' Map.empty Map.empty []

        let Just eTy = tyInf e''

        expectedTy <- parseIo exp "Nat"
        let expectedTy' = undermodule expectedTy modul
        expectedTy'' <- runCIo modul $ elabInf expectedTy' Map.empty Map.empty []

        Dynamic.Erase.e eTy @?= Dynamic.Erase.e expectedTy''

        en <- runCIo modul $ cbvCheck e''

        expecteden <- parseIo exp "5"
        let expecteden' = undermodule expecteden modul
        expecteden'' <- runCIo modul $ elabInf expecteden' Map.empty Map.empty []

        Dynamic.Erase.e en @?= Dynamic.Erase.e expecteden''
        ,
      testCase "rep" $ do
        Ok (ddefs,trmdefs) <- loadFile file2
        let modul = makeMod ddefs trmdefs
        e <- parseIo exp "rep Bool true 3"
        let e' = undermodule e modul
        e'' <- runCIo modul $ elabInf e' Map.empty Map.empty []

        let Just eTy = tyInf e''

        expectedTy <- parseIo exp "Vec Bool 3"
        let expectedTy' = undermodule expectedTy modul
        expectedTy'' <- runCIo modul $ elabInf expectedTy' Map.empty Map.empty []

        Dynamic.Erase.e eTy @?= Dynamic.Erase.e expectedTy''

        en <- runCIo modul $ cbvCheck e''

        expecteden <- parseIo exp "[true,true,true]<Bool>"
        let expecteden' = undermodule expecteden modul
        expecteden'' <- runCIo modul $ elabInf expecteden' Map.empty Map.empty []

        Dynamic.Erase.e en @?= Dynamic.Erase.e expecteden''
        ,

      testCase "head" $ do
        Ok (ddefs,trmdefs) <- loadFile file2
        let modul = makeMod ddefs trmdefs
        e <- parseIo exp "head Bool 2 [false,true,false]<Bool>" 
        let e' = undermodule e modul
        e'' <- runCIo modul $ elabInf e' Map.empty Map.empty []

        let Just eTy = tyInf e''

        expectedTy <- parseIo exp "Bool"
        let expectedTy' = undermodule expectedTy modul
        expectedTy'' <- runCIo modul $ elabInf expectedTy' Map.empty Map.empty []

        Dynamic.Erase.e eTy @?= Dynamic.Erase.e expectedTy''

        en <- runCIo modul $ cbvCheck e''

        expecteden <- parseIo exp "false"
        let expecteden' = undermodule expecteden modul
        expecteden'' <- runCIo modul $ elabInf expecteden' Map.empty Map.empty []

        Dynamic.Erase.e en @?= Dynamic.Erase.e expecteden''
        ,

     testCase "okFun" $ do
        Ok (ddefs,trmdefs) <- loadFile file2
        let modul = makeMod ddefs trmdefs
        e <- parseIo exp "okFun 3" 
        let e' = undermodule e modul
        e'' <- runCIo modul $ elabInf e' Map.empty Map.empty []

        let Just eTy = tyInf e''

        expectedTy <- parseIo exp "Bool"
        let expectedTy' = undermodule expectedTy modul
        expectedTy'' <- runCIo modul $ elabInf expectedTy' Map.empty Map.empty []

        Dynamic.Erase.e eTy @?= Dynamic.Erase.e expectedTy''

        en <- runCIo modul $ cbvCheck e''

        expecteden <- parseIo exp "true"
        let expecteden' = undermodule expecteden modul
        expecteden'' <- runCIo modul $ elabInf expecteden' Map.empty Map.empty []

        Dynamic.Erase.e en @?= Dynamic.Erase.e expecteden''
      ],

    testGroup file3 [
      testCase "add" $ do
        Ok (ddefs,trmdefs) <- loadFile file3
        let modul = makeMod ddefs trmdefs
        e <- parseIo exp "add 2 3"
        let e' = undermodule e modul
        e'' <- runCIo modul $ elabInf e' Map.empty Map.empty []

        let Just eTy = tyInf e''

        expectedTy <- parseIo exp "Nat"
        let expectedTy' = undermodule expectedTy modul
        expectedTy'' <- runCIo modul $ elabInf expectedTy' Map.empty Map.empty []

        Dynamic.Erase.e eTy @?= Dynamic.Erase.e expectedTy''

        en <- runCIo modul $ cbvCheck e''

        expecteden <- parseIo exp "5"
        let expecteden' = undermodule expecteden modul
        expecteden'' <- runCIo modul $ elabInf expecteden' Map.empty Map.empty []

        Dynamic.Erase.e en @?= Dynamic.Erase.e expecteden''
        ,
      testCase "rep" $ do
        Ok (ddefs,trmdefs) <- loadFile file3
        let modul = makeMod ddefs trmdefs
        e <- parseIo exp "rep Bool true 3"
        let e' = undermodule e modul
        e'' <- runCIo modul $ elabInf e' Map.empty Map.empty []

        let Just eTy = tyInf e''

        expectedTy <- parseIo exp "Vec Bool 3"
        let expectedTy' = undermodule expectedTy modul
        expectedTy'' <- runCIo modul $ elabInf expectedTy' Map.empty Map.empty []

        Dynamic.Erase.e eTy @?= Dynamic.Erase.e expectedTy''

        en <- runCIo modul $ cbvCheck e''

        expecteden <- parseIo exp "[true,true,true]<Bool>"
        let expecteden' = undermodule expecteden modul
        expecteden'' <- runCIo modul $ elabInf expecteden' Map.empty Map.empty []

        Dynamic.Erase.e en @?= Dynamic.Erase.e expecteden''
        ,

      testCase "head" $ do
        Ok (ddefs,trmdefs) <- loadFile file3
        let modul = makeMod ddefs trmdefs
        e <- parseIo exp "head Bool 2 [false,true,false]<Bool>" 
        let e' = undermodule e modul
        e'' <- runCIo modul $ elabInf e' Map.empty Map.empty []

        let Just eTy = tyInf e''

        expectedTy <- parseIo exp "Bool"
        let expectedTy' = undermodule expectedTy modul
        expectedTy'' <- runCIo modul $ elabInf expectedTy' Map.empty Map.empty []

        Dynamic.Erase.e eTy @?= Dynamic.Erase.e expectedTy''

        en <- runCIo modul $ cbvCheck e''

        expecteden <- parseIo exp "false"
        let expecteden' = undermodule expecteden modul
        expecteden'' <- runCIo modul $ elabInf expecteden' Map.empty Map.empty []

        Dynamic.Erase.e en @?= Dynamic.Erase.e expecteden''
        ,


    --  testCase "append" $ do
    --     Ok (ddefs,trmdefs) <- loadFile file3
    --     let modul = makeMod ddefs trmdefs
    --     e <- parseIo exp "append Nat 2 [1,2]<Nat> 3 [7,8,9]<Nat>" 
    --     let e' = undermodule e modul
    --     e'' <- runCIo modul $ elabInf e' Map.empty Map.empty []

    --     let Just eTy = tyInf e''
    --     eTy' <- runCIo modul $ cbvCheck eTy

    --     expectedTy <- parseIo exp "Vec Nat 5"
    --     let expectedTy' = undermodule expectedTy modul
    --     expectedTy'' <- runCIo modul $ elabInf expectedTy' Map.empty Map.empty []

    --     Dynamic.Erase.e eTy' @?= Dynamic.Erase.e expectedTy'' --TODO more direct test of eqaality

    --     en <- runCIo modul $ cbvCheck e''

    --     expecteden <- parseIo exp "[1,2,7,8,9]<Nat>"
    --     let expecteden' = undermodule expecteden modul
    --     expecteden'' <- runCIo modul $ elabInf expecteden' Map.empty Map.empty []

    --     Dynamic.Erase.e en @?= Dynamic.Erase.e expecteden'',

    --  testCase "revapp" $ do
    --     Ok (ddefs,trmdefs) <- loadFile file3
    --     let modul = makeMod ddefs trmdefs
    --     e <- parseIo exp "revapp Nat 2 [1,2]<Nat> 3 [7,8,9]<Nat>" 
    --     let e' = undermodule e modul
    --     e'' <- runCIo modul $ elabInf e' Map.empty Map.empty []

    --     let Just eTy = tyInf e''
    --     eTy' <- runCIo modul $ cbvCheck eTy

    --     expectedTy <- parseIo exp "Vec Nat 5"
    --     let expectedTy' = undermodule expectedTy modul
    --     expectedTy'' <- runCIo modul $ elabInf expectedTy' Map.empty Map.empty []

    --     Dynamic.Erase.e eTy' @?= Dynamic.Erase.e expectedTy'' --TODO more direct test of eqaality

    --     en <- runCIo modul $ cbvCheck e''

    --     expecteden <- parseIo exp "[2,1,7,8,9]<Nat>"
    --     let expecteden' = undermodule expecteden modul
    --     expecteden'' <- runCIo modul $ elabInf expecteden' Map.empty Map.empty []

    --     Dynamic.Erase.e en @?= Dynamic.Erase.e expecteden'',

     testCase "okFun" $ do
        Ok (ddefs,trmdefs) <- loadFile file3
        let modul = makeMod ddefs trmdefs
        e <- parseIo exp "okFun 3" 
        let e' = undermodule e modul
        e'' <- runCIo modul $ elabInf e' Map.empty Map.empty []

        let Just eTy = tyInf e''

        expectedTy <- parseIo exp "Bool"
        let expectedTy' = undermodule expectedTy modul
        expectedTy'' <- runCIo modul $ elabInf expectedTy' Map.empty Map.empty []

        Dynamic.Erase.e eTy @?= Dynamic.Erase.e expectedTy''

        en <- runCIo modul $ cbvCheck e''

        expecteden <- parseIo exp "true"
        let expecteden' = undermodule expecteden modul
        expecteden'' <- runCIo modul $ elabInf expecteden' Map.empty Map.empty []

        Dynamic.Erase.e en @?= Dynamic.Erase.e expecteden''
        ,

      testCase "badd" $ do
        Ok (ddefs,trmdefs) <- loadFile file3
        let modul = makeMod ddefs trmdefs
        e <- parseIo exp "badd 2 3"
        let e' = undermodule e modul
        e'' <- runCIo modul $ elabInf e' Map.empty Map.empty []

        let Just eTy = tyInf e''

        expectedTy <- parseIo exp "Nat"
        let expectedTy' = undermodule expectedTy modul
        expectedTy'' <- runCIo modul $ elabInf expectedTy' Map.empty Map.empty []

        Dynamic.Erase.e eTy @?= Dynamic.Erase.e expectedTy''

        en <- runCIo modul $ cbvCheck e''

        expecteden <- parseIo exp "5"
        let expecteden' = undermodule expecteden modul
        expecteden'' <- runCIo modul $ elabInf expecteden' Map.empty Map.empty []

        Dynamic.Erase.e en @?= Dynamic.Erase.e expecteden''

        e2 <- parseIo exp "badd 1 3"
        let e2' = undermodule e2 modul
        e2'' <- runCIo modul $ elabInf e2' Map.empty Map.empty []
        en2 <- runCIo modul $ cbvCheck e2''

        expecteden2 <- parseIo exp "0"
        let expecteden2' = undermodule expecteden2 modul
        expecteden2'' <- runCIo modul $ elabInf expecteden2' Map.empty Map.empty []

        Dynamic.Erase.e en2 @?= Dynamic.Erase.e expecteden2''
        ,

      testCase "test" $ do
        Ok (ddefs,trmdefs) <- loadFile file3
        let modul = makeMod ddefs trmdefs
        e <- parseIo exp "test"
        let e' = undermodule e modul
        e'' <- runCIo modul $ elabInf e' Map.empty Map.empty []

        let Just eTy = tyInf e''

        expectedTy <- parseIo exp "Bool"
        let expectedTy' = undermodule expectedTy modul
        expectedTy'' <- runCIo modul $ elabInf expectedTy' Map.empty Map.empty []

        Dynamic.Erase.e eTy @?= Dynamic.Erase.e expectedTy''

        let Left (Msg s _) = runC (cbvCheck e'') modul Nothing

        assertBool "message not empty" $ not (null s)
        ,

      testCase "badFun" $ do
        Ok (ddefs,trmdefs) <- loadFile file3
        let modul = makeMod ddefs trmdefs
        e <- parseIo exp "badFun 3"
        let e' = undermodule e modul
        e'' <- runCIo modul $ elabInf e' Map.empty Map.empty []

        let Just eTy = tyInf e''

        expectedTy <- parseIo exp "Bool"
        let expectedTy' = undermodule expectedTy modul
        expectedTy'' <- runCIo modul $ elabInf expectedTy' Map.empty Map.empty []

        Dynamic.Erase.e eTy @?= Dynamic.Erase.e expectedTy''

        let Left (Msg s _) = runC (cbvCheck e'') modul Nothing

        assertBool "message not empty" $ not (null s)
        ,

      testCase "almostFun" $ do
        Ok (ddefs,trmdefs) <- loadFile file3
        let modul = makeMod ddefs trmdefs
        e <- parseIo exp "almostFun 3"
        let e' = undermodule e modul
        e'' <- runCIo modul $ elabInf e' Map.empty Map.empty []

        let Just eTy = tyInf e''

        expectedTy <- parseIo exp "Bool"
        let expectedTy' = undermodule expectedTy modul
        expectedTy'' <- runCIo modul $ elabInf expectedTy' Map.empty Map.empty []

        en <- runCIo modul $ cbvCheck e''
        expecteden <- parseIo exp "true"
        let expecteden' = undermodule expecteden modul
        expecteden'' <- runCIo modul $ elabInf expecteden' Map.empty Map.empty []

        Dynamic.Erase.e en @?= Dynamic.Erase.e expecteden''

        e2 <- parseIo exp "almostFun 1"
        let e2' = undermodule e2 modul
        e2'' <- runCIo modul $ elabInf e2' Map.empty Map.empty []

        let Left (Msg s _) = runC (cbvCheck e2'') modul Nothing

        assertBool "message not empty" $ not (null s)
    ]
  ]