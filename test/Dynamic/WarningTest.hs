

module Dynamic.WarningTest where


import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless.Internal.Fold (foldMapOf, toListOf)
import Unbound.Generics.LocallyNameless.Unsafe (unsafeUnbind)

import Data.Map (Map)
import qualified Data.Map as Map

import Dynamic.Ast

import Unbound.Generics.LocallyNameless.Unsafe (unsafeUnbind)
import Control.Monad.Writer
import Control.Monad.Identity
import Dynamic.Norm
import UnboundHelper
import SourcePos
import Dynamic.Eq
import PreludeHelper
import Dynamic.ElabBase
import Dynamic.Visitor
import GHC.Generics
import Data.Data
import AlphaShow
import Unbound.Generics.LocallyNameless.Ignore (Ignore(I))


import Dynamic.Warning

import Test.Tasty (defaultMain, testGroup, TestTree)
import Test.Tasty.HUnit (Assertion(..), assertEqual, assertBool, testCase)

import Unbound.Generics.LocallyNameless.Unsafe (unsafeUnbind)


tests :: TestTree
tests =
  testGroup "warn tests"
     [testCase "no warning without assert" $ do
        assertEqual "unchanged syntax, exmpty warning list" (TyU, []) (rwf $ visitFresh visitorWarnSame TyU)
-- todo could be extended to any syntax witout an assert
     , testCase "detects no warning" $ do
        let (e,w) = rwf $ visitFresh visitorWarnSame $ efun
        assertEqual "unchanged syntax, exmpty warning list" (TyU, []) (rwf $ visitFresh visitorWarnSame TyU)
     , testCase "detects a warning" $ do
        let (e,w) = rwf $ visitFresh visitorWarnSame $ efun
        assertEqual "unchanged syntax, exmpty warning list" (TyU, []) (rwf $ visitFresh visitorWarnSame TyU)
     , testCase "detects a warning even though it could have been eraserd" $ do
        let e = initSame Nothing TyU TyU TyU 
        let (e',w) = rwf $ visitFresh visitorWarnSame $ e
        assertEqual "unchanged syntax" e' e
        assertBool "unchanged syntax, exmpty warning list" $ 1 <= length w
     , testCase "extracts from inside same assertions" $ do
        let e = initSame Nothing TyU TyU (initSame Nothing (initSame Nothing TyU TyU TyU) TyU TyU )
        let (e',w) = rwf $ visitFresh visitorWarnSame $ e
        assertEqual "unchanged syntax" e' e
        assertBool "unchanged syntax, exmpty warning list" $ 1 <= length w
     ]

efun = Fun $ bind (s2n "f",s2n "x") $ initSame Nothing TyU TyU (V $  s2n "x")

rwf :: Monoid w => FreshMT (WriterT w Identity) a -> (a, w)
rwf e = runIdentity $ runWriterT $ runFreshMT $ e
