module Dynamic.Ex3 where

import AlphaShow
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Dynamic.Ast
import Dynamic.Env
import Dynamic.Erase (erase, eraseCast)
import Dynamic.Helper (runC)
import Dynamic.Norm (cbvCheck)
import SourcePos
import Unbound.Generics.LocallyNameless
import UnboundHelper
import PreludeHelper
import Debug.Trace



-- "in,"
-- let (head13,unnamed) = (s2n"head13",s2n"unnamed") in App (V head13 (An (Just (Pi (C (App (TConF "Vec" [] (An (Just (TelBnd (C (TConF "Nat" [] (An (Just (NoBnd ())))) Dummy TyU (Same TyU Dummy TyU) TyU) (bind unnamed (NoBnd ())))))) (C (App (DConF "S" [] (An (Just ("Nat", TelBnd (C (TConF "Nat" [] (An (Just (NoBnd ())))) Dummy TyU (Same TyU Dummy TyU) TyU) (bind unnamed (NoBnd [])))))) (C (DConF "Z" [] (An (Just ("Nat", NoBnd [])))) Dummy (TConF "Nat" [] (An (Just (NoBnd ())))) (Same (TConF "Nat" [] (An (Just (NoBnd ())))) Dummy (C (TConF "Nat" [] (An (Just (NoBnd ())))) Dummy TyU (Same TyU Dummy TyU) TyU)) (C (TConF "Nat" [] (An (Just (NoBnd ())))) Dummy TyU (Same TyU Dummy TyU) TyU)) (An (Just (TConF "Nat" [] (An (Just (NoBnd ()))))))) Dummy (TConF "Nat" [] (An (Just (NoBnd ())))) (Same (TConF "Nat" [] (An (Just (NoBnd ())))) Dummy (C (TConF "Nat" [] (An (Just (NoBnd ())))) Dummy TyU (Same TyU Dummy TyU) TyU)) (C (TConF "Nat" [] (An (Just (NoBnd ())))) Dummy TyU (Same TyU Dummy TyU) TyU)) (An (Just TyU))) Dummy TyU (Same TyU Dummy TyU) TyU) (bind unnamed (C (TConF "Unit" [] (An (Just (NoBnd ())))) Dummy TyU (Same TyU Dummy TyU) TyU)))))) (C (DConF "Nil" [] (An (Just ("Vec", NoBnd [DConF "Z" [] (An (Just ("Nat", NoBnd [])))])))) Dummy (TConF "Vec" [DConF "Z" [] (An (Just ("Nat", NoBnd [])))] (An (Just (NoBnd ())))) (Same (TConF "Vec" [DConF "Z" [] (An (Just ("Nat", NoBnd [])))] (An (Just (NoBnd ())))) Dummy (C (App (TConF "Vec" [] (An (Just (TelBnd (C (TConF "Nat" [] (An (Just (NoBnd ())))) Dummy TyU (Same TyU Dummy TyU) TyU) (bind unnamed (NoBnd ())))))) (C (App (DConF "S" [] (An (Just ("Nat", TelBnd (C (TConF "Nat" [] (An (Just (NoBnd ())))) Dummy TyU (Same TyU Dummy TyU) TyU) (bind unnamed (NoBnd [])))))) (C (DConF "Z" [] (An (Just ("Nat", NoBnd [])))) Dummy (TConF "Nat" [] (An (Just (NoBnd ())))) (Same (TConF "Nat" [] (An (Just (NoBnd ())))) Dummy (C (TConF "Nat" [] (An (Just (NoBnd ())))) Dummy TyU (Same TyU Dummy TyU) TyU)) (C (TConF "Nat" [] (An (Just (NoBnd ())))) Dummy TyU (Same TyU Dummy TyU) TyU)) (An (Just (TConF "Nat" [] (An (Just (NoBnd ()))))))) Dummy (TConF "Nat" [] (An (Just (NoBnd ())))) (Same (TConF "Nat" [] (An (Just (NoBnd ())))) Dummy (C (TConF "Nat" [] (An (Just (NoBnd ())))) Dummy TyU (Same TyU Dummy TyU) TyU)) (C (TConF "Nat" [] (An (Just (NoBnd ())))) Dummy TyU (Same TyU Dummy TyU) TyU)) (An (Just TyU))) Dummy TyU (Same TyU Dummy TyU) TyU)) (C (App (TConF "Vec" [] (An (Just (TelBnd (C (TConF "Nat" [] (An (Just (NoBnd ())))) Dummy TyU (Same TyU Dummy TyU) TyU) (bind unnamed (NoBnd ())))))) (C (App (DConF "S" [] (An (Just ("Nat", TelBnd (C (TConF "Nat" [] (An (Just (NoBnd ())))) Dummy TyU (Same TyU Dummy TyU) TyU) (bind unnamed (NoBnd [])))))) (C (DConF "Z" [] (An (Just ("Nat", NoBnd [])))) Dummy (TConF "Nat" [] (An (Just (NoBnd ())))) (Same (TConF "Nat" [] (An (Just (NoBnd ())))) Dummy (C (TConF "Nat" [] (An (Just (NoBnd ())))) Dummy TyU (Same TyU Dummy TyU) TyU)) (C (TConF "Nat" [] (An (Just (NoBnd ())))) Dummy TyU (Same TyU Dummy TyU) TyU)) (An (Just (TConF "Nat" [] (An (Just (NoBnd ()))))))) Dummy (TConF "Nat" [] (An (Just (NoBnd ())))) (Same (TConF "Nat" [] (An (Just (NoBnd ())))) Dummy (C (TConF "Nat" [] (An (Just (NoBnd ())))) Dummy TyU (Same TyU Dummy TyU) TyU)) (C (TConF "Nat" [] (An (Just (NoBnd ())))) Dummy TyU (Same TyU Dummy TyU) TyU)) (An (Just TyU))) Dummy TyU (Same TyU Dummy TyU) TyU)) (An (Just (C (TConF "Unit" [] (An (Just (NoBnd ())))) Dummy TyU (Same TyU Dummy TyU) TyU)))
-- "clean,"
-- let unnamed=s2n"unnamed" in Same (TConF "Vec" [DConF "Z" [] (An (Just ("Nat", NoBnd [])))] (An (Just (NoBnd ())))) Dummy (C (App (TConF "Vec" [] (An (Just (TelBnd (C (TConF "Nat" [] (An (Just (NoBnd ())))) Dummy TyU (Same TyU Dummy TyU) TyU) (bind unnamed (NoBnd ())))))) (C (App (DConF "S" [] (An (Just ("Nat", TelBnd (C (TConF "Nat" [] (An (Just (NoBnd ())))) Dummy TyU (Same TyU Dummy TyU) TyU) (bind unnamed (NoBnd [])))))) (C (DConF "Z" [] (An (Just ("Nat", NoBnd [])))) Dummy (TConF "Nat" [] (An (Just (NoBnd ())))) (Same (TConF "Nat" [] (An (Just (NoBnd ())))) Dummy (C (TConF "Nat" [] (An (Just (NoBnd ())))) Dummy TyU (Same TyU Dummy TyU) TyU)) (C (TConF "Nat" [] (An (Just (NoBnd ())))) Dummy TyU (Same TyU Dummy TyU) TyU)) (An (Just (TConF "Nat" [] (An (Just (NoBnd ()))))))) Dummy (TConF "Nat" [] (An (Just (NoBnd ())))) (Same (TConF "Nat" [] (An (Just (NoBnd ())))) Dummy (C (TConF "Nat" [] (An (Just (NoBnd ())))) Dummy TyU (Same TyU Dummy TyU) TyU)) (C (TConF "Nat" [] (An (Just (NoBnd ())))) Dummy TyU (Same TyU Dummy TyU) TyU)) (An (Just TyU))) Dummy TyU (Same TyU Dummy TyU) TyU)
-- let unnamed=s2n"unnamed" in TConF "Vec" [Same (DConF "Z" [] (An (Just ("Nat", NoBnd [])))) Dummy (C (App (DConF "S" [] (An (Just ("Nat", TelBnd (C (TConF "Nat" [] (An (Just (NoBnd ())))) Dummy TyU (Same TyU Dummy TyU) TyU) (bind unnamed (NoBnd [])))))) (C (DConF "Z" [] (An (Just ("Nat", NoBnd [])))) Dummy (TConF "Nat" [] (An (Just (NoBnd ())))) (Same (TConF "Nat" [] (An (Just (NoBnd ())))) Dummy (C (TConF "Nat" [] (An (Just (NoBnd ())))) Dummy TyU (Same TyU Dummy TyU) TyU)) (C (TConF "Nat" [] (An (Just (NoBnd ())))) Dummy TyU (Same TyU Dummy TyU) TyU)) (An (Just (TConF "Nat" [] (An (Just (NoBnd ()))))))) Dummy (TConF "Nat" [] (An (Just (NoBnd ())))) (Same (TConF "Nat" [] (An (Just (NoBnd ())))) Dummy (C (TConF "Nat" [] (An (Just (NoBnd ())))) Dummy TyU (Same TyU Dummy TyU) TyU)) (C (TConF "Nat" [] (An (Just (NoBnd ())))) Dummy TyU (Same TyU Dummy TyU) TyU))] (An Nothing)
-- "cleaned,"
--
cleaned = let (head13,unnamed) = (s2n"head13",s2n"unnamed") in 
  App (V head13 (An (Just (Pi (C (App (TConF "Vec" [] (An (Just (TelBnd (C (TConF "Nat" [] (An (Just (NoBnd ())))) Dummy TyU (Same TyU Dummy TyU) TyU) (bind unnamed (NoBnd ())))))) (C (App (DConF "S" [] (An (Just ("Nat", TelBnd (C (TConF "Nat" [] (An (Just (NoBnd ())))) Dummy TyU (Same TyU Dummy TyU) TyU) (bind unnamed (NoBnd [])))))) (C (DConF "Z" [] (An (Just ("Nat", NoBnd [])))) Dummy (TConF "Nat" [] (An (Just (NoBnd ())))) (Same (TConF "Nat" [] (An (Just (NoBnd ())))) Dummy (C (TConF "Nat" [] (An (Just (NoBnd ())))) Dummy TyU (Same TyU Dummy TyU) TyU)) (C (TConF "Nat" [] (An (Just (NoBnd ())))) Dummy TyU (Same TyU Dummy TyU) TyU)) (An (Just (TConF "Nat" [] (An (Just (NoBnd ()))))))) Dummy (TConF "Nat" [] (An (Just (NoBnd ())))) (Same (TConF "Nat" [] (An (Just (NoBnd ())))) Dummy (C (TConF "Nat" [] (An (Just (NoBnd ())))) Dummy TyU (Same TyU Dummy TyU) TyU)) (C (TConF "Nat" [] (An (Just (NoBnd ())))) Dummy TyU (Same TyU Dummy TyU) TyU)) (An (Just TyU))) Dummy TyU (Same TyU Dummy TyU) TyU) (bind unnamed (C (TConF "Unit" [] (An (Just (NoBnd ())))) Dummy TyU (Same TyU Dummy TyU) TyU))))))
   (C (DConF "Nil" [] (An (Just ("Vec", NoBnd [DConF "Z" [] (An (Just ("Nat", NoBnd [])))])))) 
      Dummy 
      (TConF "Vec" [DConF "Z" [] (An (Just ("Nat", NoBnd [])))] (An (Just (NoBnd ()))))
      (TConF "Vec" [Same (DConF "Z" [] (An (Just ("Nat", NoBnd [])))) 
                         Dummy 
                         (C (App (DConF "S" [] (An (Just ("Nat", TelBnd (C (TConF "Nat" [] (An (Just (NoBnd ())))) Dummy TyU (Same TyU Dummy TyU) TyU) (bind unnamed (NoBnd [])))))) 
                              (C (DConF "Z" [] (An (Just ("Nat", NoBnd [])))) Dummy (TConF "Nat" [] (An (Just (NoBnd ())))) (Same (TConF "Nat" [] 
                              (An (Just (NoBnd ())))) Dummy 
                              (C (TConF "Nat" [] (An (Just (NoBnd ())))) Dummy TyU (Same TyU Dummy TyU) TyU)) 
                              (C (TConF "Nat" [] (An (Just (NoBnd ())))) Dummy TyU (Same TyU Dummy TyU) TyU)) (An (Just (TConF "Nat" [] (An (Just (NoBnd ()))))))) Dummy (TConF "Nat" [] (An (Just (NoBnd ())))) (Same (TConF "Nat" [] (An (Just (NoBnd ())))) Dummy (C (TConF "Nat" [] (An (Just (NoBnd ())))) Dummy TyU (Same TyU Dummy TyU) TyU)) (C (TConF "Nat" [] (An (Just (NoBnd ())))) Dummy TyU (Same TyU Dummy TyU) TyU))] (An Nothing)) (App (TConF "Vec" [] (An (Just (TelBnd (C (TConF "Nat" [] (An (Just (NoBnd ())))) Dummy TyU (Same TyU Dummy TyU) TyU) (bind unnamed (NoBnd ())))))) (App (DConF "S" [] (An (Just ("Nat", TelBnd (C (TConF "Nat" [] (An (Just (NoBnd ())))) Dummy TyU (Same TyU Dummy TyU) TyU) (bind unnamed (NoBnd [])))))) (DConF "Z" [] (An (Just ("Nat", NoBnd [])))) (An (Just (TConF "Nat" [] (An (Just (NoBnd ()))))))) (An (Just TyU))))
   (An (Just (C (TConF "Unit" [] (An (Just (NoBnd ())))) Dummy TyU (Same TyU Dummy TyU) TyU)))





out = Case [DConF "Nil" [] (An (Just ("Vec", NoBnd [DConF "Z" [] (An (Just ("Nat", NoBnd [])))])))] (An Nothing) [] (Just 
 debugSR
 ) (An (Just (C (TConF "Unit" [] (An (Just (NoBnd ())))) Dummy TyU (Same TyU Dummy TyU) TyU)))


info = Info debugSR Base Map.empty (ignore TyU) (ignore TyU)