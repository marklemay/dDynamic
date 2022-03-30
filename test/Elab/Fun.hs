module Elab.Fun where


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

import Test.Tasty.HUnit (Assertion(..), assertEqual, assertBool, testCase, HasCallStack)

import Unbound.Generics.LocallyNameless.Unsafe (unsafeUnbind)
import Ast
import UnboundHelper


import Parser.Common
import Parser.Fun ( showParses )

import Debug.Trace

import qualified Dynamic.Ast as C
import qualified Dynamic.Norm as C
import qualified Dynamic.Err as C
import qualified Dynamic.Elab as C
import qualified Dynamic.ElabModule as C
import qualified Dynamic.Env as C
import qualified Dynamic.Helper as C
-- import qualified Dynamic.Erase as C
-- import qualified Dynamic.Clean as C
-- import qualified Dynamic.Warn as C
import ParserMonad
import qualified Parser as P
import SourcePos
import qualified GHC.OverloadedLabels as Map
import Erase
import Data.Either (isRight)
import Unbound.Generics.LocallyNameless.Bind

-- properties
--  cast soundness
--   progress
--   preservation
--  Garentee (backed by erasure)
--   X erasure 
--   elabs to well cast
--   welltyped terms elab
--   never blame welltyped terms
--   consitent eval



-- TODO (HasCallStack) 
x =~= y = counterexample (show x ++ " not alpha equivalent to " ++ show y ++ 
    "\n" ++ codeshow x ++
    "\n" ++ codeshow y) (x == y)


-- isRight :: HasCallStack => (Applicative f, Show a1) => Either a1 a2 -> f a2
-- isRight (Right a) = pure a
-- isRight (Left e) = error $ show e


elabErases :: Exp -> Property
elabErases e = do
  undefined
  -- let se = simpleShow True e 0 
  -- let Right ee = prettyParse "" se P.exp
  -- case C.runC (do
  --           ce <- C.elabInf e 
  --             -- give enough ctx for unbound vars
  --             (Map.fromList [(s2n "x", C.TyU), (s2n "y", C.TyU), (s2n "z", C.TyU)]) 
  --             (Map.fromList [(s2n "x", s2n "x"), (s2n "y", s2n "y"), (s2n "z", s2n "z")]) 
  --             []
  --           C.erase ce) C.emptyModule (Just $ SourceRange (Just se) (SourcePos "" 0 0) (endPos "" se))
  --           of
  --   Left x -> discard 
  --   Right ce -> erase e =~= ce

elabErases' :: Exp -> Property
elabErases' e = do
  undefined
  -- let se = simpleShow True e 0 
  -- let Right ee = prettyParse "" se P.exp
  -- case C.runC (do
  --           ce <- C.elabInf e 
  --             -- give enough ctx for unbound vars
  --             (Map.empty) 
  --             (Map.empty) 
  --             []
  --           C.erase ce) C.emptyModule (Just $ SourceRange (Just se) (SourcePos "" 0 0) (endPos "" se))
  --           of
  --   Left x -> discard 
  --   Right ce -> erase e =~= ce

sameCheck :: C.Exp -> Bool -> Bool 
sameCheck = undefined
-- sameCheck (C.Same _ _ _ ) u = u
-- sameCheck (C.C uu _ uty wty topTy) u = sameCheck uu u && sameCheck uty u && sameCheck wty True && sameCheck uty u 
-- sameCheck (C.Fun (B p bod) _) u = sameCheck bod u
-- sameCheck (C.App f a _) u = sameCheck f u && sameCheck a u
-- sameCheck _ u = True

-- sameok :: Exp -> Property
-- sameok e = do
--   let se = simpleShow True e 0 
--   let Right ee = prettyParse "" se P.exp
--   case C.runC (do
--             ce <- C.elabInf e 
--               -- give enough ctx for unbound vars
--               (Map.empty) 
--               (Map.empty) 
--               []
--             pure ce) C.emptyModule (Just $ SourceRange (Just se) (SourcePos "" 0 0) (endPos "" se))
--             of
--     Left x -> discard 
--     Right ce -> counterexample (show ce) (sameCheck ce False)



tests :: TestTree
tests =
  testGroup "elab the functional fragment"
     [testProperty "erasure matches" $ elabErases,
      testProperty "erasure matches (empty ctx)" $ elabErases'
      -- ,
      -- testProperty "structureal check" $ sameok
       ]
