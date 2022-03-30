module Dynamic.TestEnv (stdModule, nat, n, vecU, idN) where

import Data.Map (Map)
import qualified Data.Map as Map

import Data.Set (Set)
import qualified Data.Set as Set

import Dynamic.Env
import UnboundHelper 
import Dynamic.Ast
import Unbound.Generics.LocallyNameless
import Dynamic.ElabBase


empModule = Module{dataCtx=Map.empty, defCtx=DefCtx Map.empty}

--TODO rename this
stdModule = Module{dataCtx=dataCtx', defCtx=DefCtx Map.empty}

dataCtx' = Map.fromList [
  ("Unit", DataDef (NoBnd ()) $ Map.fromList [("tt", NoBnd [])] ),
  ("Bool", DataDef (NoBnd ()) $ Map.fromList [("true", NoBnd []),("false", NoBnd [])] ),
  ("Nat", DataDef (NoBnd ()) $ Map.fromList [("Z", NoBnd []),("S", (TelBnd nat $ u $ NoBnd []))] ),

  ("Id", DataDef (TelBnd TyU $ bind x $ TelBnd (V x) $ u $ TelBnd (V x) $ u$ NoBnd ()) $ Map.fromList [("refl", TelBnd TyU $ bind x $ TelBnd (V x) $ bind y $ NoBnd [V x, V y, V y])] ),
  --dumb version for testing
  ("VecU", DataDef (TelBnd nat $ u $ NoBnd ()) $ Map.fromList [("NilU", NoBnd [n 0]),("ConsU", (TelBnd nat $ bind x $ TelBnd (vecU (V x)) $ u $ NoBnd [s $ V x ]))] ),

  ("IdN", DataDef (TelBnd nat $ u $ TelBnd nat $ u$ NoBnd ()) $ Map.fromList [("reflN", TelBnd nat $ bind x $ NoBnd [V x, V x])] )
  ] 
 --  DataDef (Tel Term Ty ()) (Map DCName (Tel Term Ty [Term])) deriving (


y = s2n "y"
x = s2n "x"
nat = TConF "Nat" [] (NoBnd ()) (NoBnd ())

n 0 = DConF "Z" [] ("Nat", NoBnd []) (NoBnd ()) (NoBnd ())
n i = s $ n (i - 1)

s x = DConF "S" [x] ("Nat", NoBnd []) (TelBnd nat $ u $ NoBnd ()) (NoBnd ())

bool = TConF "Bool" [] (NoBnd ()) (NoBnd ())

vecU x = TConF "VecU" [x] (NoBnd ()) (TelBnd nat $ u $ NoBnd ())

vec x = TConF "vec" [x] (NoBnd ()) (TelBnd nat $ u $ NoBnd ())

id a a1 a2 = TConF "Id" [a, a1, a2] (NoBnd ()) (TelBnd TyU $ bind x $ TelBnd (V x) $ u $ TelBnd (V x) $ u $ NoBnd ())

idN a1 a2 = TConF "IdN" [a1, a2] (NoBnd ()) (TelBnd nat $ u $ TelBnd nat $ u $ NoBnd ())



-- data Unit : * {
--   | tt  : Unit
-- };

-- data Bool : * {
--   | true  : Bool
--   | false : Bool
-- };

-- data Nat : * {
--   | Z : Nat
--   | S : Nat -> Nat
-- };
