{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DeriveDataTypeable, DeriveGeneric, MultiParamTypeClasses, FlexibleContexts, FlexibleInstances, DeriveFunctor, RankNTypes, LambdaCase  #-}

module Parser.Common where

import Data.Maybe

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
import Ast
import UnboundHelper

fullShrink s ss = shrink
  where
  shrink TyU = [] -- can't get simpler
  shrink (Solve _) = [TyU] 
  shrink (V _) = [TyU] 
  shrink (TCon _) = [TyU] 
  shrink (DCon _) = [TyU] 
  shrink (Pi aTy (unsafeUnbind-> (a, bodTy))) = 
    [aTy, bodTy] -- does the problem persist with the binder removed?
    ++ [Pi aTy' $ bind a bodTy' | (aTy', bodTy') <- s (aTy, bodTy) ] -- shrink under the binder
  shrink (Fun (bndBod@(unsafeUnbind-> (_, bod)))) = 
    -- [substsssBind bndBod TyU TyU] -- does the problem persist with the binder removed?
    [bod]
      ++ (Fun <$> underBinder shrink bndBod) -- shrink under the binder
  shrink (e1 ::: e2) = [e1, e2] ++ [e1' ::: e2' | (e1',e2') <- s (e1, e2)]
  shrink (f `App` a) = [f, a] ++ [f' `App` a' | (f',a') <- s (f,a)]
  -- shrink (Case scrut (An ann) branches) = 
  --   [scrut]++  fmap (snd . unsafeUnbind) (maybeToList  ann)
  --    ++ fmap (\ (Match _ (unsafeUnbind-> (_, bod))) -> bod) branches
  --    ++ [Case scrut' (An ann') branches' | (scrut', ann', branches') <- ss (scrut, ann, branches) ]
  shrink _ = []


-- TODO: underBinder, underBinderM
-- TODO: move to unboundHelper
underBinder op bndExp = let 
  (p, bod) = unsafeUnbind bndExp -- Should be safe since no freshnames are invoked
  in do
    bod' <- op bod
    pure $ bind p bod'