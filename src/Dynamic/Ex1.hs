{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
module Dynamic.Ex1 where
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

y = s2n "y'"
mx = s2n "mx"
mx' = s2n "mx'"



r e =  runIdentity $ runExceptT $ runFreshMT $ runWithModuleMT (runWithSourceLocMT' e ) stdModule
e1 :: Either C.Err (C.Exp, C.Ty)
e1 = r $ elabInf TyU $ empElabInfo pure
e2 = r $ elabInf (TyU ::: TyU) $ empElabInfo pure
e3 = r $ elabCast (TyU ::: TyU) C.TyU $ empElabInfo pure
e4 = r $ elabCast (TyU ::: (Pi TyU $ u $ TyU)) C.TyU $ empElabInfo pure

e5 = r $ elabInf ((lam x $ V x) ::: (Pi TyU $ u $ TyU)) $ empElabInfo pure
e6 = r $ elabInf (TCon "Unit") $ empElabInfo pure
e7 = r $ elabInf (DCon "tt") $ empElabInfo pure
e8 = r $ elabInf (DCon "S" `App` DCon "Z") $ empElabInfo pure
e9 = r $ elabInf (DCon "NilU") $ empElabInfo pure
-- e = r $ elabInf TyU empElabInfo


Right ee1 = r $ checkTelMaybe 
  [V x, V mx] 
  (TelBnd (Just TyU) $ bind y $ TelBnd (Just $ V y) $ u $ NoBnd TyU) 
  ((empElabInfo pure) {
  varMap=Map.fromList ([(x, x'),(mx, mx')]),
  tyCtx=Map.fromList ([(x', C.TyU), (mx', C.V x')])
  }) Map.empty