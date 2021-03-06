module Dynamic.Ex3 where
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
y = s2n "y"
z = s2n "z"
p = s2n "p"
q= s2n "q"

bool = C.TConF "Bool" [] (NoBnd ()) (NoBnd ())


id a a1 a2 = C.TConF "Id" [a, a1, a2] (NoBnd ()) (TelBnd C.TyU $ bind x $ TelBnd (C.V x) $ u $ TelBnd (C.V x) $ u $ NoBnd ())

r e =  runIdentity $ runExceptT $ runFreshMT $ runWithModuleMT (runWithSourceLocMT' e) stdModule

e1 = r $ getPat (PVar x) nat (empElabInfo pure) 
e2 = r $ getPats ([PVar x, PVar y]) (TelBnd nat $ bind z $ TelBnd (vecU $ C.V z) $ u $ NoBnd $ C.V z) (empElabInfo pure) 
e3 = r $ getPat (Pat "S" [PVar x]) nat (empElabInfo pure) 

e40 = r $ getPat (Pat "NilU" []) (vecU (n 1)) (empElabInfo pure) 
e4 = r $ getPat (Pat "reflN" [PVar x]) (idN (n 0) (n 0)) (empElabInfo pure) 

-- e2 = r $ getPats ([PVar x, PVar y]) nat (empElabInfo pure) 
-- Right let (p,y) = (s2n"p",s2n"y") in 
--   [Equation (V y) (V y) (Union (Tcon 0 (V p)) TyU (Tcon 0 (V p))) 
--     (Union (Tcon 1 (V p)) (Union (Tcon 0 (V p)) TyU (Tcon 0 (V p))) (Union (Tcon 2 (V p)) (Union (Tcon 0 (V p)) TyU (Tcon 0 (V p))) (V y)))] 
--     fromList [(x, (V y, Tcon 0 (V p), Tcon 1 (V p)))] [] 
--   [Equation (TConF "Nat" [] (NoBnd ()) (NoBnd ())) (TConF "Bool" [] (NoBnd ()) (NoBnd ())) TyU (Union (TConF "Nat" [] (NoBnd ()) (NoBnd ())) (Union TyU TyU TyU) (Union (Tcon 0 (V p)) (Union TyU TyU TyU) (TConF "Bool" [] (NoBnd ()) (NoBnd ()))))]

-- TODO

-- e6 = r $ fOUni' empElabInfo $ initProb (Set.fromList [x]) [Equation (vec $ V x) (vec $ V x) TyU (V p)] 

