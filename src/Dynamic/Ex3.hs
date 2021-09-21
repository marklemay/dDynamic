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



-- let _=s2n"_" in Same (TConF "Vec" [DConF "Z" [] (An (Just ("Nat", NoBnd [])))] (An (Just (NoBnd ())))) info (C (App (TConF "Vec" [] (An (Just (TelBnd (C (TConF "Nat" [] (An (Just (NoBnd ())))) info TyU (Same TyU info TyU) TyU) (bind _ (NoBnd ())))))) (C (App (DConF "S" [] (An (Just ("Nat", TelBnd (C (TConF "Nat" [] (An (Just (NoBnd ())))) info TyU (Same TyU info TyU) TyU) (bind _ (NoBnd [])))))) (C (DConF "Z" [] (An (Just ("Nat", NoBnd [])))) info (TConF "Nat" [] (An (Just (NoBnd ())))) (Same (TConF "Nat" [] (An (Just (NoBnd ())))) info (C (TConF "Nat" [] (An (Just (NoBnd ())))) info TyU (Same TyU info TyU) TyU)) (C (TConF "Nat" [] (An (Just (NoBnd ())))) info TyU (Same TyU info TyU) TyU)) (An (Just (TConF "Nat" [] (An (Just (NoBnd ()))))))) info (TConF "Nat" [] (An (Just (NoBnd ())))) (Same (TConF "Nat" [] (An (Just (NoBnd ())))) info (C (TConF "Nat" [] (An (Just (NoBnd ())))) info TyU (Same TyU info TyU) TyU)) (C (TConF "Nat" [] (An (Just (NoBnd ())))) info TyU (Same TyU info TyU) TyU)) (An (Just TyU))) info TyU (Same TyU info TyU) TyU)
-- let _=s2n"_" in TConF "Vec" [Same (DConF "Z" [] (An (Just ("Nat", NoBnd [])))) info (C (App (DConF "S" [] (An (Just ("Nat", TelBnd (C (TConF "Nat" [] (An (Just (NoBnd ())))) info TyU (Same TyU info TyU) TyU) (bind _ (NoBnd [])))))) (C (DConF "Z" [] (An (Just ("Nat", NoBnd [])))) info (TConF "Nat" [] (An (Just (NoBnd ())))) (Same (TConF "Nat" [] (An (Just (NoBnd ())))) info (C (TConF "Nat" [] (An (Just (NoBnd ())))) info TyU (Same TyU info TyU) TyU)) (C (TConF "Nat" [] (An (Just (NoBnd ())))) info TyU (Same TyU info TyU) TyU)) (An (Just (TConF "Nat" [] (An (Just (NoBnd ()))))))) info (TConF "Nat" [] (An (Just (NoBnd ())))) (Same (TConF "Nat" [] (An (Just (NoBnd ())))) info (C (TConF "Nat" [] (An (Just (NoBnd ())))) info TyU (Same TyU info TyU) TyU)) (C (TConF "Nat" [] (An (Just (NoBnd ())))) info TyU (Same TyU info TyU) TyU))] (An Nothing)
-- "cleaned,"
-- let (head13,_) = (s2n"head13",s2n"_") in App (V head13 (An (Just (Pi (C (App (TConF "Vec" [] (An (Just (TelBnd (C (TConF "Nat" [] (An (Just (NoBnd ())))) info TyU (Same TyU info TyU) TyU) (bind _ (NoBnd ())))))) (C (App (DConF "S" [] (An (Just ("Nat", TelBnd (C (TConF "Nat" [] (An (Just (NoBnd ())))) info TyU (Same TyU info TyU) TyU) (bind _ (NoBnd [])))))) (C (DConF "Z" [] (An (Just ("Nat", NoBnd [])))) info (TConF "Nat" [] (An (Just (NoBnd ())))) (Same (TConF "Nat" [] (An (Just (NoBnd ())))) info (C (TConF "Nat" [] (An (Just (NoBnd ())))) info TyU (Same TyU info TyU) TyU)) (C (TConF "Nat" [] (An (Just (NoBnd ())))) info TyU (Same TyU info TyU) TyU)) (An (Just (TConF "Nat" [] (An (Just (NoBnd ()))))))) info (TConF "Nat" [] (An (Just (NoBnd ())))) (Same (TConF "Nat" [] (An (Just (NoBnd ())))) info (C (TConF "Nat" [] (An (Just (NoBnd ())))) info TyU (Same TyU info TyU) TyU)) (C (TConF "Nat" [] (An (Just (NoBnd ())))) info TyU (Same TyU info TyU) TyU)) (An (Just TyU))) info TyU (Same TyU info TyU) TyU) (bind _ (C (TConF "Unit" [] (An (Just (NoBnd ())))) info TyU (Same TyU info TyU) TyU)))))) (C (DConF "Nil" [] (An (Just ("Vec", NoBnd [DConF "Z" [] (An (Just ("Nat", NoBnd [])))])))) info (TConF "Vec" [DConF "Z" [] (An (Just ("Nat", NoBnd [])))] (An (Just (NoBnd ())))) (TConF "Vec" [Same (DConF "Z" [] (An (Just ("Nat", NoBnd [])))) info (C (App (DConF "S" [] (An (Just ("Nat", TelBnd (C (TConF "Nat" [] (An (Just (NoBnd ())))) info TyU (Same TyU info TyU) TyU) (bind _ (NoBnd [])))))) (C (DConF "Z" [] (An (Just ("Nat", NoBnd [])))) info (TConF "Nat" [] (An (Just (NoBnd ())))) (Same (TConF "Nat" [] (An (Just (NoBnd ())))) info (C (TConF "Nat" [] (An (Just (NoBnd ())))) info TyU (Same TyU info TyU) TyU)) (C (TConF "Nat" [] (An (Just (NoBnd ())))) info TyU (Same TyU info TyU) TyU)) (An (Just (TConF "Nat" [] (An (Just (NoBnd ()))))))) info (TConF "Nat" [] (An (Just (NoBnd ())))) (Same (TConF "Nat" [] (An (Just (NoBnd ())))) info (C (TConF "Nat" [] (An (Just (NoBnd ())))) info TyU (Same TyU info TyU) TyU)) (C (TConF "Nat" [] (An (Just (NoBnd ())))) info TyU (Same TyU info TyU) TyU))] (An Nothing)) (App (TConF "Vec" [] (An (Just (TelBnd (C (TConF "Nat" [] (An (Just (NoBnd ())))) info TyU (Same TyU info TyU) TyU) (bind _ (NoBnd ())))))) (App (DConF "S" [] (An (Just ("Nat", TelBnd (C (TConF "Nat" [] (An (Just (NoBnd ())))) info TyU (Same TyU info TyU) TyU) (bind _ (NoBnd [])))))) (DConF "Z" [] (An (Just ("Nat", NoBnd [])))) (An (Just (TConF "Nat" [] (An (Just (NoBnd ()))))))) (An (Just TyU)))) (An (Just (C (TConF "Unit" [] (An (Just (NoBnd ())))) info TyU (Same TyU info TyU) TyU)))




out = Case [C (DConF "Nil" [] (An (Just ("Vec", NoBnd [DConF "Z" [] (An (Just ("Nat", NoBnd [])))])))) info 
              (TConF "Vec" [DConF "Z" [] (An (Just ("Nat", NoBnd [])))] (An (Just (NoBnd ())))) 
              (TConF "Vec" [Same (DConF "Z" [] (An (Just ("Nat", NoBnd [])))) info 
                                 (C (App (DConF "S" [] (An (Just ("Nat", TelBnd (C (TConF "Nat" [] (An (Just (NoBnd ())))) info TyU (Same TyU info TyU) TyU) (bind unnamed (NoBnd [])))))) (C (DConF "Z" [] (An (Just ("Nat", NoBnd [])))) info (TConF "Nat" [] (An (Just (NoBnd ())))) (Same (TConF "Nat" [] (An (Just (NoBnd ())))) info (C (TConF "Nat" [] (An (Just (NoBnd ())))) info TyU (Same TyU info TyU) TyU)) (C (TConF "Nat" [] (An (Just (NoBnd ())))) info TyU (Same TyU info TyU) TyU)) (An (Just (TConF "Nat" [] (An (Just (NoBnd ())))))))
                                    info 
                                    (TConF "Nat" [] (An (Just (NoBnd ())))) 
                                    (Same (TConF "Nat" [] (An (Just (NoBnd ())))) info (C (TConF "Nat" [] (An (Just (NoBnd ())))) info TyU (Same TyU info TyU) TyU)) 
                                    (C (TConF "Nat" [] (An (Just (NoBnd ())))) info TyU (Same TyU info TyU) TyU))] (An Nothing)) (TConF "Vec" [DConF "S" [DConF "Z" [] (An (Just ("Nat", NoBnd [])))] (An (Just ("Nat", NoBnd [])))] (An (Just (NoBnd ()))))] (An Nothing) [] (Just (SourceRange (Just "\n\ndata Unit : * {\n  | tt  : Unit\n};\n\ndata Nat : * {\n  | Z : Nat\n  | S : Nat -> Nat\n};\n\n\n-- length indexed lists\ndata Vec : Nat -> * {\n  | Nil  : Vec 0\n  | Cons : Unit -> (n : Nat) -> Vec n -> Vec (S n)\n};\n\n\nhead : Vec 1 -> Unit ;\nhead v = \n  case v <_ => Unit >{\n   | (Cons a _ _) => a\n   } ;\n\n\n\naf : Unit ;\naf = head Nil ;\n-- make sure cbv still works\n-- truns out this will only work once coverage is implemented\n") (SourcePos "ex/e3.dt" 21 2) (SourcePos "ex/e3.dt" 23 5))) (An (Just (C (TConF "Unit" [] (An (Just (NoBnd ())))) info TyU (Same TyU info TyU) TyU)))





info = Info debugSR Base Map.empty (ignore TyU) (ignore TyU)


exr =
  runC
    ( do
        e <- cbvCheck out
        erase e
    )
    emptyModule
    Nothing

e1 = C (DConF "Nil" [] (An (Just ("Vec", NoBnd [DConF "Z" [] (An (Just ("Nat", NoBnd [])))])))) info 
              (TConF "Vec" [DConF "Z" [] (An (Just ("Nat", NoBnd [])))] (An (Just (NoBnd ())))) 
              (TConF "Vec" [Same (DConF "Z" [] (An (Just ("Nat", NoBnd [])))) info 
                                 (C (App (DConF "S" [] (An (Just ("Nat", TelBnd (C (TConF "Nat" [] (An (Just (NoBnd ())))) info TyU (Same TyU info TyU) TyU) (bind unnamed (NoBnd [])))))) (C (DConF "Z" [] (An (Just ("Nat", NoBnd [])))) info (TConF "Nat" [] (An (Just (NoBnd ())))) (Same (TConF "Nat" [] (An (Just (NoBnd ())))) info (C (TConF "Nat" [] (An (Just (NoBnd ())))) info TyU (Same TyU info TyU) TyU)) (C (TConF "Nat" [] (An (Just (NoBnd ())))) info TyU (Same TyU info TyU) TyU)) (An (Just (TConF "Nat" [] (An (Just (NoBnd ())))))))
                                    info 
                                    (TConF "Nat" [] (An (Just (NoBnd ())))) 
                                    (Same (TConF "Nat" [] (An (Just (NoBnd ())))) info (C (TConF "Nat" [] (An (Just (NoBnd ())))) info TyU (Same TyU info TyU) TyU)) 
                                    (C (TConF "Nat" [] (An (Just (NoBnd ())))) info TyU (Same TyU info TyU) TyU))] (An Nothing)
                                    
                                    ) (TConF "Vec" [DConF "S" [DConF "Z" [] (An (Just ("Nat", NoBnd [])))] (An (Just ("Nat", NoBnd [])))] (An (Just (NoBnd ()))))


exr1 =
  runC
    ( do
        e <- cbvCheck e1
        erase e
    )
    emptyModule
    Nothing

e2 = 
    Same (DConF "Z" [] (An (Just ("Nat", NoBnd [])))) info 
          (C (App (DConF "S" [] (An (Just ("Nat", TelBnd (C (TConF "Nat" [] (An (Just (NoBnd ())))) info TyU (Same TyU info TyU) TyU) (bind unnamed (NoBnd [])))))) (C (DConF "Z" [] (An (Just ("Nat", NoBnd [])))) info (TConF "Nat" [] (An (Just (NoBnd ())))) (Same (TConF "Nat" [] (An (Just (NoBnd ())))) info (C (TConF "Nat" [] (An (Just (NoBnd ())))) info TyU (Same TyU info TyU) TyU)) (C (TConF "Nat" [] (An (Just (NoBnd ())))) info TyU (Same TyU info TyU) TyU)) (An (Just (TConF "Nat" [] (An (Just (NoBnd ())))))))
                                    info 
                                    (TConF "Nat" [] (An (Just (NoBnd ())))) 
                                    (Same (TConF "Nat" [] (An (Just (NoBnd ())))) info (C (TConF "Nat" [] (An (Just (NoBnd ())))) info TyU (Same TyU info TyU) TyU)) 
                                    (C (TConF "Nat" [] (An (Just (NoBnd ())))) info TyU (Same TyU info TyU) TyU))



exr2 =
  runC
    ( do
        e <- cbvCheck e2
        pure $ lfullshow e
        -- erase e
    )
    emptyModule
    Nothing