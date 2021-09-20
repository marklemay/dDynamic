module Ex where
import Unbound.Generics.LocallyNameless
import Dynamic.Ast
import UnboundHelper

-- ex = 
--   let (ex38,u_) = (s2n"ex38",s2n"u_") 
--   in V ex38 (An (Just (C 
--     (App (TConF "Bs" [] (An (Just (TelBnd (C (TConF "B" [] (An (Just (NoBnd ())))) Dummy TyU (Same TyU Base TyU) TyU) (bind u_ (NoBnd ())))))) 
--     (C (DConF "t" [] (An (Just ("B", NoBnd [])))) Dummy (TConF "B" [] (An (Just (NoBnd ())))) (Same (TConF "B" [] (An (Just (NoBnd ())))) Base (C (TConF "B" [] (An (Just (NoBnd ())))) Dummy TyU (Same TyU Base TyU) TyU)) (C (TConF "B" [] (An (Just (NoBnd ())))) Dummy TyU (Same TyU Base TyU) TyU)) (An (Just TyU)))
--      Dummy TyU (Same TyU Base TyU) TyU)))