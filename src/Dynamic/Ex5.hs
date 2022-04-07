{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# LANGUAGE FlexibleContexts #-}
module Dynamic.Ex5 where

import Dynamic.Ast 
-- import qualified Dynamic.Env as C --TODO clean
import Dynamic.Env
import Dynamic.Unification
-- import Dynamic.Norm (whnf)
import AlphaShow

import Data.Map (Map)
import qualified Data.Map as Map

import Data.Set (Set)
import qualified Data.Set as Set

import Unbound.Generics.LocallyNameless
import Control.Monad.Except
import Unbound.Generics.LocallyNameless.Unsafe (unsafeUnbind)

import UnboundHelper
import Dynamic.Elab
import Dynamic.Unification
import Control.Lens (Identity(runIdentity))
import Helper
import Prelude hiding (id)
import Dynamic.ElabBase

import PreludeHelper
import qualified StdLib as E
import Dynamic.ElabModule hiding (stdlibIO')
import Dynamic.TestEnv (stdModule)


import Dynamic.Patttern hiding (x)

r :: WithSourceLocMT (WithModuleMT (FreshMT (ExceptT e Identity))) a
  -> Either e a
r e =  runIdentity $ runExceptT $ runFreshMT $ runWithModuleMT (runWithSourceLocMT' e ) stdModule



x = s2n "x"
y = s2n "y"
z = s2n "z"
z' = s2n "z'"


px = s2n "px"
px' = s2n "px'"
px1 = s2n "px1"
px2 = s2n "px2"
px3 = s2n "px3"

e0 = r $ subPat (Pat "t" [] px) (Pat "f" [] px)
e01 = r $ subPat (Pat "t" [] px) (Pat "t" [] px)
e02 = r $ subPat (PVar x) (Pat "f" [] px)
e03 = r $ subPat (Pat "f" [] px) (PVar x)

e1 = r $ subPats' [(Pat "t" [] px)] [(Pat "f" [] px)]
e11 = r $ subPats' [(Pat "t" [] px)] [(Pat "t" [] px)]
e12 = r $ subPats' [(PVar x)] [(Pat "f" [] px)]
e13 = r $ subPats' [(Pat "f" [] px)] [(PVar x)]

e2 = r $ subPats' [PVar x,PVar y] [Pat "t" [] px, Pat "t" [] px']
e21 = r $ subPats' [Pat "t" [] px, Pat "t" [] px'] [Pat "t" [] px, Pat "t" [] px']
e22 = r $ subPats' [Pat "t" [] px, Pat "t" [] px'] [PVar x,PVar y]
e23 = r $ subPats' [PVar x, Pat "f" [] px'] [Pat "t" [] px, Pat "t" [] px'] 
e24 = r $ subPats' [PVar x, Pat "t" [] px'] [Pat "t" [] px, PVar y]


e3 = r $ subPat (Pat "Z" [] px) (PVar x)
e31 = r $ subPat (PVar x) (Pat "S" [Pat "Z" [] px'] px)
e32 = r $ subPat (PVar x) (Pat "S" [(Pat "S" [Pat "Z" [] px'] px) ] px)
e33 = r $ subPat (PVar x) (Pat "S" [(Pat "S" [PVar y] px') ] px)