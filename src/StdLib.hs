module StdLib (
  stdlib,
  -- add, sym, trans, cong, pair, tt,
  -- vec, unit, ls, head, rep, two, tcon,
  bool,
  n, s, ls, nat
  ) where

import Prelude hiding (head)

import Unbound.Generics.LocallyNameless

import Data.Map (Map)
import qualified Data.Map as Map

import Ast
import UnboundHelper
import Helper
import Env


add = s2n "add"
sym = s2n "sym"
trans = s2n "trans"
cong = s2n "cong"
pair = s2n "pair"
first = s2n "first"
second = s2n "second"
head = s2n "head"
rep = s2n "rep"
two = s2n "two"


-- internal names
a = s2n "a"
a' = s2n "a'"
aTy = s2n "aTy"
aTy' = s2n "aTy'"
b = s2n "b"
x = s2n "x"
xx = s2n "xx"
y = s2n "y"
yy = s2n "yy"
z = s2n "z"
xy = s2n "xy"
yz = s2n "yz"
az = s2n "az"
inty = s2n "inty"
outty = s2n "outty"
p = s2n "p"
ih = s2n "ih"
f = s2n "f"

stdlib :: TyEnv
stdlib = TyEnv Map.empty 
  (Map.fromList [
    ("Empty", DataDef (NoBnd ()) $ Map.fromList []),
    ("Unit", DataDef (NoBnd ()) $ Map.fromList [
      ("tt", NoBnd [])]),
    ("Bool", DataDef (NoBnd ()) $ Map.fromList [
      ("true", NoBnd []),
      ("false", NoBnd [])]),
    ("Nat", DataDef (NoBnd ()) $ Map.fromList [
      ("Z", NoBnd []),
      ("S", TelBnd nat $ u $ NoBnd [])]),
    ("Id", DataDef (TelBnd TyU $ bind a $ TelBnd (V a) $ u $ TelBnd (V a) $ u $ NoBnd ()) $ Map.fromList [
      ("Refl", TelBnd TyU $ bind a $ TelBnd (V a) $ bind x $ NoBnd [V a, V x, V x])]),
    ("Vec", DataDef (TelBnd TyU $ u $ TelBnd nat $ u $ NoBnd ()) $ Map.fromList [-- length indexed vector, good for examples
      ("Nil", TelBnd TyU $ bind aTy $ NoBnd [V aTy, n 0]),
      ("Cons", TelBnd TyU $ bind aTy $ TelBnd (V aTy) $ u $ TelBnd nat $ bind x $ TelBnd (tcon "Vec" [V aTy, V x]) $ u $ NoBnd [V aTy, s $ V x])]),
    ("Sigma", DataDef (TelBnd TyU $ bind aTy $ TelBnd (V aTy --> TyU) $ u $ NoBnd ()) $ Map.fromList [
      ("Tuple", TelBnd TyU $ bind aTy $ TelBnd (V aTy --> TyU) $ bind p $ TelBnd (V aTy) $ bind a $ TelBnd (V p `App` V a) $ u $ NoBnd [V aTy, V p])]),
  -- Singletons
    ("Sing", DataDef (TelBnd TyU $ bind a $ TelBnd (V a) $ u $ NoBnd $ ()) $ Map.fromList [
      ("mkSing", TelBnd TyU $ bind a $ TelBnd (V a) $ bind x $ NoBnd [V a,V x])]),
    ("SB", DataDef (TelBnd bool $ u $ NoBnd ()) $ Map.fromList [
      ("mkSB", TelBnd bool $ bind x $ NoBnd [V x])])
   ])
  (Map.fromList [
    -- (add, (let x = s2n "x"
    --            y = s2n "y"
    --            x' = s2n "x'"
    --        in lam x $ lam y $ 
    --             Case (V x) (ann $ bind (unnamed, []) nat) [ -- TODO let the weak inference handle this
    --               Match "Z" $ bind []   $ V y,
    --               Match "S" $ bind [x'] $ s $ V add `App` V x' `App` V y],
    --        nat --> (nat --> nat) )),
    -- (sym, (lam aTy $ lam x $ lam y $ lam xy $ 
    --          Case (V xy) (ann $ bind (unnamed, [aTy, x,y]) $ tcon "Id" [V aTy, V y, V x])
    --            [Match "Refl" $ bind [aTy,a] $ DCon "Refl" `App` V aTy `App` V a],
    --        Pi TyU $ bind aTy $ Pi (V aTy) $ bind x $ Pi (V aTy) $ bind y $ tcon "Id" [V aTy, V x, V y] --> tcon "Id" [V aTy, V y, V x] )),
    -- (trans, (lam aTy $ lam x $ lam y $ lam xy $
    --            Case (V xy) (ann $ bind (unnamed, [aTy,a,a']) $  (Pi (V aTy) $ bind z $ tcon "Id" [V aTy, V a', V z] --> tcon "Id" [V aTy, V a, V z]))
    --              [Match "Refl" $ bind [aTy,a] $ lam (unnamed) $ lam az $ V az],
    --        Pi TyU $ bind aTy $ Pi (V aTy) $ bind x $Pi (V aTy) $ bind y $ tcon "Id" [V aTy, V x, V y] --> (Pi (V aTy) $ bind z $ tcon "Id" [V aTy, V y, V z] -->  tcon "Id" [V aTy, V x, V z]))),
    -- (cong, (lam inty $ lam outty $ lam x $ lam y $ lam xy $
    --           Case (V xy) (ann $ bind (unnamed, [inty, x,y]) $ Pi (V inty --> V outty) $ bind f $ tcon "Id" [V outty, V f `App` V x, V f `App` V y])
    --             [Match "Refl" $ bind [unnamed, a] $  lam f $ DCon "Refl" `App`  V outty `App` (V f `App` V a) ],
    --        Pi TyU $ bind inty $ Pi TyU $ bind outty $ Pi (V inty) $ bind x $ Pi (V inty) $ bind y $ (tcon "Id" [V inty, V x, V y]) --> ( Pi (V inty --> V outty) $ bind f $ tcon "Id" [V outty, V f `App` V x, V f `App` V y]))),
    -- (head, (
    --     lam outty $ lam x $ lam y $ Case (V y) (An $ Just $ bind (unnamed, [aTy', y]) $ 
    --       Case (V y) (An $ Just $ bind (unnamed,[]) TyU) [
    --       Match "Z" $ bind [] unit,
    --       Match "S" $ bind [unnamed] $ V aTy'
    --       ]
        
    --     ) [-- TODO seems like this should be inferable without the annotation
    --       Match "Nil" $ bind [aTy] tt,
    --       Match "Cons" $ bind [aTy,a,x,xx] $ V a
    --     ]
    --     ,
    --        Pi TyU $ bind outty $ Pi nat $ bind x $ Pi (tcon "Vec" [V outty, s $ V x]) $ u $ V outty)),
    -- (rep, (lam aTy $ lam a $ lam x $ 
    --           Case (V x) (ann $ bind (x, []) $ tcon "Vec" [V aTy, V x])
    --             [Match "Z" $ bind []  $ DCon "Nil" `App` V aTy,
    --              Match "S" $ bind [y] $  DCon "Cons" `App` V aTy `App` V a `App` V y `App` (V rep `App` V aTy `App` V a `App` V y )],
    --        Pi TyU $ bind aTy $ V aTy --> (Pi nat $ bind x $ tcon "Vec" [V aTy, V x]) )),

    -- (pair, (lam inty $ lam outty $ lam x $ lam y $
    --           DCon "Tuple" `App`  V inty `App` lam (s2n "_") (V outty) `App` V x `App` V y,
    --        Pi TyU $ bind inty $ Pi TyU $ bind outty $ V inty -->  (V outty -->  tcon "Sigma" [V inty , lam (s2n "_") $ V outty]))),
    -- (first, (lam aTy $ lam p $ lam xy $
    --             Case (V xy) (ann $ bind (s2n "_", [aTy, p]) $ V aTy)
    --             [Match "Tuple" $ bind [s2n "_",s2n "_",a, s2n "_"] $ V a],
    --        Pi TyU $ bind aTy $ Pi (V aTy --> TyU) $ bind p $ tcon "Sigma" [V aTy, V p] --> V aTy)),
    -- (second, (lam aTy $ lam p $ lam xy $ 
    --             Case (V xy) (ann $ bind (xy, [aTy, p]) $ V p `App` (V first `App` V aTy `App` V p `App` V xy))
    --             [Match "Tuple" $ bind [s2n "_",s2n "_",s2n "_", b] $ V b],
    --        Pi TyU $ bind aTy $ Pi (V aTy --> TyU) $ bind p $ Pi (tcon "Sigma" [V aTy, V p]) $ bind xy $ (V p `App` (V first `App` V aTy `App` V p `App` V xy)) ))
   ])


--replacement constructors
n :: Integer -> Term
n x | x < 0  = error "Not a nat!"
n 0 = DCon "Z"
n x = s $ n $ x - 1

s x =  DCon "S" `App` x 
nat = TCon "Nat"


-- vec ty l = tcon "Vec" [ty, l]

-- unit :: Exp
-- unit = tcon "Unit" []
-- tt = DCon "tt"

bool = tcon "Bool" []

ls [] ty = DCon "Nil" `App` ty
ls (h:tl) ty = DCon "Cons" `App` ty  `App` h `App` (n $ fromIntegral $ length tl) `App` (ls tl ty)


tcon s args = TCon s `apps` args
