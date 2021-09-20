module Erase where

import Ast
import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless.Bind
import UnboundHelper


erase :: Exp -> Exp
erase (Pos _ e _) = erase e
erase (e ::: t) = erase e
erase (Fun (B p bod)) = Fun (B p $ erase bod)
erase (e `App` t) = erase e `App` erase t
erase (Case s ann bs) = 
  Case (erase <$> s) (noAn) $ (\ (Match (B p bod)) -> Match (B p $ erase bod)) <$> bs 
erase (Pi aTy ((B p bod))) = Pi (erase aTy) $ B p $ erase bod
-- erasePos (V x) = V x
-- erasePos TyU = TyU
erase x = x

-- e :: Term -> Term
-- e = runFreshM . erase

-- TODo typeclass?
-- remove all type and pos info
-- erase :: Fresh m => Exp -> m Exp
-- erase (Pos _ e _) = erase e 
-- erase (Pi x bndTy) = erase e 
-- erase (e ::: _) = erase e 
-- erase e = pure e 