{-# LANGUAGE QuasiQuotes #-}

-- TODO move to tests

module Examples where

import Prelude hiding((^^), exp, pi, pred)
import Parser
import ParserMonad
import Env
import Ast
import StdLib
import Norm
import Ty

import Text.RawString.QQ

--parse, tycheck and run
pstd :: String -> Maybe (Exp, String)
pstd = parse $ do
  e <- token exp 
  pure $ undermodule e (dataCtx stdlib)


-- parse and run
rstd s = 
  case pstd s of
    Just (e, "") -> runTcMonad stdlib $ eval e


-- parse and run

tystd s = 
  case pstd s of
    Just (e, "") -> runTcMonad stdlib $ tyInfer e


-- parse, typcheck and run
rtystd s = 
  case pstd s of
    Just (e, "") -> runTcMonad stdlib $ do
       ty <- tyInfer e
       ev <- eval e
       pure (ev,ty)



-- can parse "standard" cc things 
cctrue = rtystd [r|
  ((\a => \y => \ z => y) : (a:*) -> a -> a -> a)
    *
    (*->*) 
    *
|]

-- some syntactic sugar to work with the std lib
num = rtystd [r|
  add 7 2
|]

vect = rtystd [r|
  [1,2,3,4] <Nat>
|]


-- supports general recursion
bad = tystd [r|
  (fun f x => add x (f x))
  : (Nat -> Nat)
|]


-- supports type : type
tyinty = rtystd [r|
  * : *
|]


-- supports elimination
pred = rtystd[r|
  case 2 {
   | Z => 0
   | S x => x
  } : Nat
|]

-- supports dependent elimination
vec1 = rtystd [r|
  case 2 < x:Nat => Vec * x> {
   | Z => rep * * 0
   | S x => rep * (* -> *) (S x)
  }
|]

vec2 = rtystd [r|
  case (rep * * 3) < _ : Vec A x => A -> Vec A (S x) > {
   | Nil A           => \ a  => rep A a 1
   | Cons A a n rest => \ a1 => Cons A a (S n) (Cons A a1 n rest)
  } (* -> *)
|]


-- you sand stub things out with ?
vec2stub = rtystd [r|
  case (rep * * 3) < _ : Vec A x => A -> Vec A (S x) > {
   | Nil A           => \ a  => rep A a 1
   | Cons A a n rest => \ a1 => ?
  } (* -> *)
|]



-- you sand stub things out with ?

fullmodule = pmstd [r|

data boool : * {
  | ttrue : boool
  | flasle : boool
  | maybe : boool -> boool
};

data wierd : (A : *) -> A -> *  {
  | wha    : wierd * *
  | just   : (A : *) -> (a:A) -> wierd A a
  };

not : boool -> boool ;
not x = case x {
  | ttrue => flasle
  | flasle => ttrue
  | maybe b => maybe (not b)
};

|]




pmstd = parse $ do
  e <- token modulep 
  pure $ undermodule e (dataCtx stdlib)



-- see https://kseo.github.io/posts/2014-02-06-multi-line-strings-in-haskell.html