module Dynamic.Ex4 where
import GHC.Stack

import Ast
import qualified Env as E
import qualified Dynamic.Ast as C
import qualified Dynamic.Norm as C
import qualified Dynamic.Err as C
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
import Control.Lens (Identity(runIdentity))
import Helper
import Dynamic.TestEnv
import Dynamic.ElabBase


-- r :: FreshM (WithModuleMT (ExceptT e (WithSourceLocMT Identity)) a)
--   -> Either e a
-- r e = runIdentity $ runWithSourceLocMT' $ runExceptT $ runWithModuleMT (runFreshM e) emptyModule
  -- runWithModuleMT runFreshM (runExceptT (ExceptT e m a) e)
x = s2n "x"
x' = s2n "x'"

xty = s2n "X"
y = s2n "y"
z = s2n "z"
p = s2n "p"
q= s2n "q"

bool = C.TConF "Bool" [] (NoBnd ()) (NoBnd ())


id a a1 a2 = C.TConF "Id" [a, a1, a2] (NoBnd ()) (TelBnd C.TyU $ bind x $ TelBnd (C.V x) $ u $ TelBnd (C.V x) $ u $ NoBnd ())

r e =  runIdentity $ runExceptT $ runFreshMT $ runWithModuleMT (runWithSourceLocMT' e) stdModule

e1 = r $ elabInf (V x) $ (empElabInfo pure) {
  varMap=Map.fromList [(x,x')],
  tyCtx=Map.fromList [(x', C.V xty)],
  Dynamic.ElabBase.assign=Map.fromList [(xty, (C.TyU,C.TyU, C.V p))]}


