{-# LANGUAGE QuasiQuotes #-}

-- TODO move to tests

module Examples where

import Prelude hiding((^^), exp, pi, pred)

import Control.Monad.Reader

import PreludeHelper
import Parser
import ParserMonad
import Env
import Ast
import StdLib
import Norm
import Ty
import Unification

import Unbound.Generics.LocallyNameless

import Text.RawString.QQ

x = s2n "x"
y = s2n "y"
z = s2n "z"


t00 = runTcMonad stdlib $ do
  removePat [PVar x] $ Pat "true" []

t01 = runTcMonad stdlib $ do
  removePat [Pat "true" []] $ Pat "true" []

t02 = runTcMonad stdlib $ do
  removePat [Pat "false" []] $ Pat "true" []

t03 = runTcMonad stdlib $ do
  removePat [Pat "false" []] $ PVar x


pn 0 = Pat "Z" []
pn x | x > 0 = Pat "S" [pn (x - 1)]

gte 0 = PVar $ s2n "_"
gte x | x > 0 = Pat "S" [gte (x - 1)]




t10 = runTcMonad stdlib $ do
  removePat [PVar x] $ pn 0 

t101 = runTcMonad stdlib $ do removePat [PVar x] $ pn 1
t1011 = runTcMonad stdlib $ do removePat [gte 1, pn 0] (pn 1)
t1012 = runTcMonad stdlib $ do removePat [gte 1] (pn 1) -- !
t1013 = runTcMonad stdlib $ do removePatsPar [gte 1] [pn 1] -- !
t1014 = runTcMonad stdlib $ do removePat [gte 1, pn 0] (pn 0) -- ok


t103 = runTcMonad stdlib $ do removePat [PVar x] $ pn 3




t11 = runTcMonad stdlib $ do
  removePat [pn 0,pn 2,pn 4] $ pn 2

t12 = runTcMonad stdlib $ do 
  removePat [PVar y] $ pn 2

t13 = runTcMonad stdlib $ do
  removePat [pn 0,pn 1,pn 2,pn 3] $ gte 2


t14 = runTcMonad stdlib $ do removePat [PVar y] $ gte 2


t20 = runTcMonad stdlib $ do
  removePat [PVar x] $ Pat "Nil" [PVar y]


t21 = runTcMonad stdlib $ do
  removePat [PVar x] $ Pat "Cons" [PVar y, PVar z, PVar (s2n "_"), PVar (s2n "_1")]


t22 = runTcMonad stdlib $ do
  removePat [PVar x] $ Pat "Cons" [PVar y, pn 0, PVar (s2n "_"), PVar (s2n "_1")]


-- t223 = runTcMonad stdlib $ do
--   removePatsPar' [(PVar (s2n "_11"), pn 0)]




e0 = runTcMonad stdlib $ do
  (ctx, _, _ ) <- unifypat' [(PVar x, bool)] [] []
  local (\ (_,s)-> (ctx,s)) $ do
    lookupTy x
-- bool

e1 = runTcMonad stdlib $ do
  (ctx, _, _ ) <- unifypat' [(Pat "S" [Pat "S" [Pat "S" [Pat "S" [PVar x]]]], nat)] [] []
  local (\ (_,s)-> (ctx,s)) $ do
    lookupTy x
-- nat

e2 = runTcMonad stdlib $ do
  (ctx, _, _ ) <- unifypat' [(Pat "mkSB" [PVar x], TCon "SB")] [] []
  local (\ (_,s)-> (ctx,s)) $ do
    lookupTy x


e30 = runTcMonad stdlib $ do
  (ctx, _, _ ) <- unifypat' [(PVar x, TCon "Sing" `App` nat)] [] []
  local (\ (_,s)-> (ctx,s)) $ do
    lookupTy x


e31 = runTcMonad stdlib $ do
  (ctx, eqs, _ ) <- unifypat' [(Pat "mkSing" [PVar x, PVar y], TCon "Sing" `App` nat)] [] []
  local (\ (_,s)-> (ctx,s)) $ do
    xty <- lookupTy x
    yty <- lookupTy y
    x' <- lookupDef' x
    y' <- lookupDef' y
    pure (xty,yty,x', y', eqs)


e321 = runTcMonad stdlib $ do
  (ctx, eqs, _ ) <- unifypat' [(Pat "mkSing" [PVar x, Pat "S" [PVar y]], TCon "Sing" `App` nat)] [] []
  local (\ (_,s)-> (ctx,s)) $ do
    ctx <- ask
    logg $ show ctx 
    xty <- lookupTy x
    logg $ show xty
    yty <- lookupTy y
    pure (xty,yty, eqs)


e322 = runTcMonad stdlib $ do
  fOUni' [(V x,nat, TyU)] [] []


e32 = runTcMonad stdlib $ do
  (ctx, eqs, _ ) <- unifypat' [(Pat "mkSing" [PVar x, Pat "S" [Pat "S" [PVar y]]], TCon "Sing" `App` nat)] [] []
  local (\ (_,s)-> (ctx,s)) $ do
    -- logg $ show ctx 
    xty <- lookupTy x
    -- logg $ show xty
    yty <- lookupTy y
    -- pure (xty,yty, eqs)
    x' <- lookupDef' x
    y' <- lookupDef' y
    pure (xty,yty,x', y', eqs)




e40 = runTcMonad stdlib $ do
  (ctx, eqs, _ ) <- unifypat' [(PVar x, TCon "Sing" `App` (TCon "Sing" `App` nat))] [] []
  local (\ (_,s)-> (ctx,s)) $ do
    -- logg $ show ctx 
    xty <- lookupTy x
    x' <- lookupDef' x
    pure (xty,x', eqs)

e41 = runTcMonad stdlib $ do
  (ctx, eqs, _ ) <- unifypat' [(Pat "mkSing" [PVar x, PVar y], TCon "Sing" `App` (TCon "Sing" `App` nat))] [] []
  local (\ (_,s)-> (ctx,s)) $ do
    -- logg $ show ctx 
    xty <- lookupTy x
    -- logg $ show xty
    yty <- lookupTy y
    -- pure (xty,yty, eqs)
    x' <- lookupDef' x
    y' <- lookupDef' y
    pure (xty,yty,x', y', eqs)

e42 = runTcMonad stdlib $ do
  (ctx, eqs, _ ) <- unifypat' [(Pat "mkSing" [PVar x, Pat "mkSing" [PVar y, PVar z]], TCon "Sing" `App` (TCon "Sing" `App` nat))] [] []
  local (\ (_,s)-> (ctx,s)) $ do
    -- logg $ show ctx 
    xty <- lookupTy x
    -- logg $ show xty
    yty <- lookupTy y
    zty <- lookupTy z
    -- pure (xty,yty, eqs)
    x' <- lookupDef' x
    y' <- lookupDef' y
    z' <- lookupDef' z
    pure (xty,yty,zty, x', y', z', eqs)

e43 = runTcMonad stdlib $ do
  (ctx, eqs, _ ) <- unifypat' [(Pat "mkSing" [PVar x, Pat "mkSing" [PVar y, Pat "S" [PVar z]]], TCon "Sing" `App` (TCon "Sing" `App` nat))] [] []
  local (\ (_,s)-> (ctx,s)) $ do
    -- logg $ show ctx 
    xty <- lookupTy x
    -- logg $ show xty
    yty <- lookupTy y
    zty <- lookupTy z
    -- pure (xty,yty, eqs)
    x' <- lookupDef' x
    y' <- lookupDef' y
    z' <- lookupDef' z
    pure (xty,yty,zty, x', y', z', eqs)

-- Copy

{-
(TyEnv {tyCtx = fromList [(x,*)], dataCtx = fromList [(\"Bool\",DataDef (NoBnd ()) (fromList [(\"false\",NoBnd []),(\"true\",NoBnd [])])),(\"Empty\",DataDef (NoBnd ()) (fromList [])),(\"Id\",DataDef (TelBnd * (<a> TelBnd 0@0 (<_> TelBnd 1@0 (<_> NoBnd ())))) (fromList [(\"Refl\",TelBnd * (<a> TelBnd 0@0 (<x> NoBnd [1@0,0@0,0@0])))])),(\"Nat\",DataDef (NoBnd ()) (fromList [(\"S\",TelBnd Nat (<_> NoBnd [])),(\"Z\",NoBnd [])])),(\"SB\",DataDef (TelBnd Bool (<_> NoBnd ())) (fromList [(\"mkSB\",TelBnd Bool (<x> NoBnd [0@0]))])),(\"Sigma\",DataDef (TelBnd * (<aTy> TelBnd 0@0 -> * (<_> NoBnd ()))) (fromList [(\"Tuple\",TelBnd * (<aTy> TelBnd 0@0 -> * (<p> TelBnd 1@0 (<a> TelBnd 1@0 0@0 (<_> NoBnd [3@0,2@0])))))])),(\"Sing\",DataDef (TelBnd * (<a> TelBnd 0@0 (<_> NoBnd ()))) (fromList [(\"mkSing\",TelBnd * (<a> TelBnd 0@0 (<x> NoBnd [1@0,0@0])))])),(\"Unit\",DataDef (NoBnd ()) (fromList [(\"tt\",NoBnd [])])),(\"Vec\",DataDef (TelBnd * (<_> TelBnd Nat (<_> NoBnd ()))) (fromList [(\"Cons\",TelBnd * (<aTy> TelBnd 0@0 (<_> TelBnd Nat (<x> TelBnd Vec 2@0 0@0 (<_> NoBnd [3@0,S 1@0]))))),(\"Nil\",TelBnd * (<aTy> NoBnd [0@0,0]))]))], 

defCtx = fromList [(x,(Nat,*))]},Nothing)
-}

-- TODO nested singletons

-- --parse, tycheck and run
-- pstd :: String -> Maybe (Exp, String)
-- pstd = parse $ do
--   e <- token exp 
--   pure $ undermodule e (dataCtx stdlib)


-- -- parse and run
-- rstd s = 
--   case pstd s of
--     Just (e, "") -> runTcMonad stdlib $ eval e


-- -- parse and run

-- tystd s = 
--   case pstd s of
--     Just (e, "") -> runTcMonad stdlib $ tyInfer e


-- -- parse, typcheck and run
-- rtystd s = 
--   case pstd s of
--     Just (e, "") -> runTcMonad stdlib $ do
--        ty <- tyInfer e
--        ev <- eval e
--        pure (ev,ty)



-- -- can parse "standard" cc things 
-- cctrue = rtystd [r|
--   ((\a => \y => \ z => y) : (a:*) -> a -> a -> a)
--     *
--     (*->*) 
--     *
-- |]

-- -- some syntactic sugar to work with the std lib
-- num = rtystd [r|
--   add 7 2
-- |]

-- vect = rtystd [r|
--   [1,2,3,4] <Nat>
-- |]


-- -- supports general recursion
-- bad = tystd [r|
--   (fun f x => add x (f x))
--   : (Nat -> Nat)
-- |]


-- -- supports type : type
-- tyinty = rtystd [r|
--   * : *
-- |]


-- -- supports elimination
-- pred = rtystd[r|
--   case 2 {
--    | Z => 0
--    | S x => x
--   } : Nat
-- |]

-- -- supports dependent elimination
-- vec1 = rtystd [r|
--   case 2 < x:Nat => Vec * x> {
--    | Z => rep * * 0
--    | S x => rep * (* -> *) (S x)
--   }
-- |]

-- vec2 = rtystd [r|
--   case (rep * * 3) < _ : Vec A x => A -> Vec A (S x) > {
--    | Nil A           => \ a  => rep A a 1
--    | Cons A a n rest => \ a1 => Cons A a (S n) (Cons A a1 n rest)
--   } (* -> *)
-- |]


-- -- you sand stub things out with ?
-- vec2stub = rtystd [r|
--   case (rep * * 3) < _ : Vec A x => A -> Vec A (S x) > {
--    | Nil A           => \ a  => rep A a 1
--    | Cons A a n rest => \ a1 => ?
--   } (* -> *)
-- |]



-- -- you sand stub things out with ?

-- fullmodule = pmstd [r|

-- data boool : * {
--   | ttrue : boool
--   | flasle : boool
--   | maybe : boool -> boool
-- };

-- data wierd : (A : *) -> A -> *  {
--   | wha    : wierd * *
--   | just   : (A : *) -> (a:A) -> wierd A a
--   };

-- not : boool -> boool ;
-- not x = case x {
--   | ttrue => flasle
--   | flasle => ttrue
--   | maybe b => maybe (not b)
-- };

-- |]




-- pmstd = parse $ do
--   e <- token modulep 
--   pure $ undermodule e (dataCtx stdlib)



-- see https://kseo.github.io/posts/2014-02-06-multi-line-strings-in-haskell.html