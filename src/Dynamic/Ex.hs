module Dynamic.Ex where

import Data.Map (Map)
import qualified Data.Map as Map

import Data.Set (Set)
import qualified Data.Set as Set

import Unbound.Generics.LocallyNameless
import Dynamic.Ast
import UnboundHelper
import Dynamic.Helper (runC)
import Dynamic.Norm (cbvCheck)
import Dynamic.Env
import AlphaShow
import SourcePos

ex = C 
  -- (DConF "Cons" 
  -- [DConF "tt" [] (An (Just ("Unit", NoBnd [])))
  --  , DConF "Z" [] (An (Just ("Nat", NoBnd [])))] 
  --  (An (Just ("Vec", NoBnd [
  --    C (App (DConF "S" [] (An (Just ("Nat", TelBnd (
  --     TConF "Nat" [] (An (Just (NoBnd ()))))
  --       (bind unnamed (NoBnd []))))))
  --       (C (DConF "Z" [] (An (Just ("Nat", NoBnd []))))
  --           info 
  --           ((TConF "Nat" [] (An (Just (NoBnd ())))) ) 
  --           (Same (C (TConF "Nat" [] (An (Just (NoBnd ())))) info TyU (Same TyU info TyU) TyU) info (C (TConF "Nat" [] (An (Just (NoBnd ())))) info TyU (Same TyU info TyU) TyU)) 
  --           (TConF "Nat" [] (An (Just (NoBnd ()))))) (An (Just (TConF "Nat" [] (An (Just (NoBnd ()))))))) 
  --     info 
  --     (TConF "Nat" [] (An (Just (NoBnd ())))) 
  --     (Same (TConF "Nat" [] (An (Just (NoBnd ())))) info (C (TConF "Nat" [] (An (Just (NoBnd ())))) info TyU (Same TyU info TyU) TyU)) 
  --     (TConF "Nat" [] (An (Just (NoBnd ()))))]))))
      (V (s2n "x") $ ann v1 )
      info 
      v1
        (TConF "Vec" [Same (C (DConF "S" [C (DConF "Z" [] (An (Just ("Nat", NoBnd []))))
                                            info
                                            (TConF "Nat" [] (An (Just (NoBnd ()))))
                                            (TConF "Nat" [] (An Nothing))
                                            (TConF "Nat" [] (An (Just (NoBnd ()))))] (An (Just ("Nat", NoBnd []))))
                              info
                              (TConF "Nat" [] (An (Just (NoBnd ()))))
                              (TConF "Nat" [] (An Nothing))
                              (TConF "Nat" [] (An (Just (NoBnd ())))))
          info 
          (DConF "S" [C (DConF "S" [C (DConF "Z" [] (An (Just ("Nat", NoBnd [])))) info (TConF "Nat" [] (An (Just (NoBnd ())))) (TConF "Nat" [] (An Nothing)) (TConF "Nat" [] (An (Just (NoBnd ()))))] 
                                  (An (Just ("Nat", NoBnd []))))
                            info
                            (TConF "Nat" [] (An (Just (NoBnd ())))) 
                            (TConF "Nat" [] (An Nothing)) 
                            (TConF "Nat" [] (An (Just (NoBnd ()))))] (An (Just ("Nat", NoBnd []))))
              ] (An Nothing))
          v2

v2 = TConF "Vec" [DConF "S" [DConF "S" [(DConF "Z" [] (An (Just ("Nat", NoBnd []))))] 
                                               (An (Just ("Nat", NoBnd [])))] 
                                  (An (Just ("Nat", NoBnd [])))
                          ] (An (Just (NoBnd ())))


v1 = TConF "Vec" [DConF "S" [(DConF "Z" [] (An (Just ("Nat", NoBnd []))))] 
                                               (An (Just ("Nat", NoBnd [])))
                          ] (An (Just (NoBnd ())))

info = Info debugSR Base Map.empty (ignore TyU) (ignore TyU)

exr = runC (cbvCheck ex) emptyModule Nothing

-- could be the lack of annotation evaluation that is doing it?