{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
module Dynamic.Ex5 where

import Dynamic.Ast 
import Dynamic.Norm 
import Dynamic.Err
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


-- Right  (stdlibIO',_) = elabModule' $ E.stdlib

-- ee = let
--         ( aTy23, p25, xy27 ) = ( s2n "aTy23", s2n "p25", s2n "xy27" ) in 
--           App ( V p25 ) -- of course won't activate in head position!
--         ( App ( App ( App ( Ref "first" ) ( V aTy23 ) ) ( V p25 ) ) ( V xy27 ) )

-- ee' = runIdentity $ runFreshMT $ runWithModuleMT (safeWhnf 100 ee) stdlibIO'

-- dee = dPrinter ee'