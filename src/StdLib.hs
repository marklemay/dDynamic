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
      ("Refl", TelBnd TyU $ bind a $ TelBnd (V a) $ bind x $ NoBnd [V a, V x, V x])])
    ,
    ("Vec", DataDef (TelBnd TyU $ u $ TelBnd nat $ u $ NoBnd ()) $ Map.fromList [-- length indexed vector, good for examples
      ("Nil", TelBnd TyU $ bind aTy $ NoBnd [V aTy, n 0]),
      ("Cons", TelBnd TyU $ bind aTy $ TelBnd (V aTy) $ u $ TelBnd nat $ bind x $ TelBnd (tcon "Vec" [V aTy, V x]) $ u $ NoBnd [V aTy, s $ V x])])
      ,
    ("Sigma", DataDef (TelBnd TyU $ bind aTy $ TelBnd (V aTy --> TyU) $ u $ NoBnd ()) $ Map.fromList [
      ("Tuple", 
      TelBnd TyU $ bind aTy $ 
      TelBnd (V aTy --> TyU) $ bind p $ 
      TelBnd (V aTy) $ bind a $
      TelBnd (V p `App` V a) $ u $
      NoBnd [V aTy, V p])])
      ,
  -- Singletons
    ("Sing", DataDef (TelBnd TyU $ bind a $ TelBnd (V a) $ u $ NoBnd $ ()) $ Map.fromList [
      ("mkSing", TelBnd TyU $ bind a $ TelBnd (V a) $ bind x $ NoBnd [V a,V x])])
      ,
    ("SB", DataDef (TelBnd bool $ u $ NoBnd ()) $ Map.fromList [
      ("mkSB", TelBnd bool $ bind x $ NoBnd [V x])])
   ])
  (Map.fromList [
    ("add", (let 
               x = s2n "x"
               y = s2n "y"
               x' = s2n "x'"
           in lam x $ lam y $ 
                Case [V x] (ann $ TelBnd (Nothing) $ u $ NoBnd nat) [ -- TODO let the weak inference handle this
                  Match $ bind  [Pat "Z" []] $ V y,
                  Match  $ bind  [Pat "S" [PVar x']] $ s $ (Ref "add") `App` V x' `App` V y],
           nat --> (nat --> nat) ))
    ,
  --  ("sym1", 
  --   let 
  --              x = s2n "x"
  --              y = s2n "y"
               
  --              xm = s2n "xm"
  --              ym = s2n "ym"

  --              xb = s2n "xb"
  --              yb = s2n "yb"
  --              ab = s2n "ab"

  --              xt = s2n "xt"
  --              yt = s2n "yt"
  --          in 
  --   (
  --     -- lam aTy $ 
  --   lam x $  lam xy $ 
  --            Case [V xy] (ann $ 
  --              TelBnd (Just (TyU)) $ bind xm $
  --              TelBnd (Just $ tcon "Sing" [TyU, V xm]) $ u $ NoBnd $ TyU
  --            )
  --              [
  --                Match $ bind [PVar xb, Pat "mkSing" [PVar aTy, PVar ab]] $ DCon "Refl" `App` V aTy `App` V ab
  --              ],
  --         --  Pi TyU $ bind aTy $ 
  --          Pi TyU $ bind xt $ 
  --         --  Pi (V aTy) $ bind xt $ 
  --          tcon "Sing" [TyU, V xt] -->
  --            TyU ))

    --   ("sym2", 
    -- let 
    --            x = s2n "x"
    --            y = s2n "y"
               
    --            xm = s2n "xm"
    --            ym = s2n "ym"

    --            xb = s2n "xb"
    --            yb = s2n "yb"
    --            ab = s2n "ab"

    --            xt = s2n "xt"
    --            yt = s2n "yt"
    --        in 
    -- (lam aTy $ 
    -- -- lam x $ 
    -- lam y $ lam xy $ 
    --          Case [V y, V xy] (ann $ 
    --           --  TelBnd (Just (V aTy)) $ bind xm $ 
    --            TelBnd (Just (V aTy)) $ bind ym $ 
    --            TelBnd (Just $ tcon "Sing" [V aTy, V ym]) $ u $ NoBnd $ tcon "Sing" [V aTy,  V ym]
    --          )
    --            [
    --              Match $ bind [PVar yb, Pat "mkSing" [PVar aTy, PVar ab]] $ DCon "mkSing" `App` V aTy `App` V ab
    --            ],
    --        Pi TyU $ bind aTy $ 
    --       --  Pi (V aTy) $ bind xt $ 
    --        Pi (V aTy) $ bind yt $ 
    --        tcon "Sing" [V aTy, V yt] -->
    --          tcon "Sing" [V aTy, V yt] ))

    ("sym", 
    let 
               x = s2n "x"
               y = s2n "y"
               
               xm = s2n "xm"
               ym = s2n "ym"

               xb = s2n "xb"
               yb = s2n "yb"
               ab = s2n "ab"

               xt = s2n "xt"
               yt = s2n "yt"
           in 
    (lam aTy $ lam x $ lam y $ lam xy $ 
             Case [V x, V y, V xy] (ann $ 
               TelBnd (Just (V aTy)) $ bind xm $ TelBnd (Just (V aTy)) $ bind ym $ 
               TelBnd (Just $ tcon "Id" [V aTy, V xm, V ym]) $ u $ NoBnd $ tcon "Id" [V aTy, V ym, V xm]
             )
               [
                 Match $ bind [PVar xb, PVar yb, Pat "Refl" [PVar aTy, PVar ab]] $ DCon "Refl" `App` V aTy `App` V ab
               ],
           Pi TyU $ bind aTy $ 
           Pi (V aTy) $ bind xt $ 
           Pi (V aTy) $ bind yt $ 
           tcon "Id" [V aTy, V xt, V yt] -->
             tcon "Id" [V aTy, V yt, V xt] ))
    ,
    ("trans", 
        let 
               x = s2n "x"
               y = s2n "y"
               z = s2n "z"
               xy = s2n "xy"
               yz = s2n "yz"
               
               xm = s2n "xm"
               ym = s2n "ym"
               zm = s2n "zm"

               xb = s2n "xb"
               yb = s2n "yb"
               zb = s2n "zb"
               aTyb = s2n "aTyb"
               aTyb' = s2n "aTyb1'"
               ab = s2n "ab"
               ab' = s2n "ab'"

               xt = s2n "xt"
               yt = s2n "yt"
           in 
    (lam aTy $ lam x $ lam y $ lam z $ lam xy $ lam yz $
               Case [V x, V y, V z, V xy, V yz] (ann $ 
               TelBnd (Just (V aTy)) $ bind xm $ TelBnd (Just (V aTy)) $ bind ym $ TelBnd (Just (V aTy)) $ bind zm $ 
                 TelBnd (Just $ tcon "Id" [V aTy, V xm, V ym]) $ u $
                 TelBnd (Just $ tcon "Id" [V aTy, V ym, V zm]) $ u $
                  NoBnd $ tcon "Id" [V aTy, V xm, V zm]
               )
                 [Match $ bind [PVar xb, PVar yb,  PVar zb, Pat "Refl" [PVar aTyb, PVar ab], Pat "Refl" [PVar aTyb', PVar ab']] $
                   DCon "Refl" `App` V aTyb `App` V ab],
           Pi TyU $ bind aTy $ Pi (V aTy) $ bind x $Pi (V aTy) $ bind y $ Pi (V aTy) $ bind z $ tcon "Id" [V aTy, V x, V y] --> (tcon "Id" [V aTy, V y, V z] -->  tcon "Id" [V aTy, V x, V z])))
    ,
  
    ("cong", 
            let 
               x = s2n "x"
               y = s2n "y"
               z = s2n "z"
               xy = s2n "xy"
               yz = s2n "yz"
               
               xm = s2n "xm"
               ym = s2n "ym"
               zm = s2n "zm"

               xb = s2n "xb"
               yb = s2n "yb"
               zb = s2n "zb"
               aTyb = s2n "aTyb"
               aTyb' = s2n "aTyb1'"
               ab = s2n "ab"
               ab' = s2n "ab'"

               xt = s2n "xt"
               yt = s2n "yt"
           in 
    (lam inty $ 
    lam outty $ 
    lam x $ 
    lam y $ 
    lam xy $ 
    lam f $
              Case [V x, V y, V xy] (ann $
               TelBnd (Just (V inty)) $ bind xm $
               TelBnd (Just (V inty)) $ bind ym $ 
                 TelBnd (Just $ tcon "Id" [V inty, V xm, V ym]) $ u $
                 NoBnd $ tcon "Id" [V outty, V f `App` V xm, V f `App` V ym]
              ) [
                Match $ bind [PVar xb, PVar yb, Pat "Refl" [PVar aTyb, PVar ab]] $
                   DCon "Refl" `App`  V outty `App` (V f `App` V ab)
                   ] ,
           Pi TyU $ bind inty $
           Pi TyU $ bind outty $
           Pi (V inty) $ bind x $
           Pi (V inty) $ bind y $
           (tcon "Id" [V inty, V x, V y]) --> ( Pi (V inty --> V outty) $ bind f $ tcon "Id" [V outty, V f `App` V x, V f `App` V y]
           )))
    ,
    ("head", 
            let 
               x = s2n "x"
               v = s2n "v"
           in (
        lam outty $ lam x $ lam v $ 
        Case [V v] (ann $ -- TODO seems like this should be inferable without the annotation
        TelBnd (Just (tcon "Vec" [V outty, s $ V x])) $ u $
        NoBnd $ V outty
        ) 
        [
          Match $ bind [Pat "Cons" [PVar aTy,PVar a,PVar x,PVar xx]] $  V a
        ]
        ,
           Pi TyU $ bind outty $ Pi nat $ bind x $ Pi (tcon "Vec" [V outty, s $ V x]) $ u $ V outty))
           ,
    ("rep", 
                let 
               x = s2n "x"
               y = s2n "y"
               z = s2n "z"
               xy = s2n "xy"
               yz = s2n "yz"
               
               xm = s2n "xm"
               ym = s2n "ym"
               zm = s2n "zm"

               xb = s2n "xb"
               yb = s2n "yb"
               zb = s2n "zb"
               aTyb = s2n "aTyb"
               aTyb' = s2n "aTyb1'"
               ab = s2n "ab"
               ab' = s2n "ab'"

               xt = s2n "xt"
               yt = s2n "yt"
           in 
    (lam aTy $ lam a $ lam x $ 
              Case [V x] (ann $ TelBnd (Just nat) $ bind xm $ NoBnd $ tcon "Vec" [V aTy, V xm])
                [
                  Match $ bind [Pat "Z" []] $ DCon "Nil" `App` V aTy
                ,
                 Match $ bind [Pat "S" [PVar y]] $ DCon "Cons" `App` V aTy `App` V a `App` V y `App` (Ref "rep" `App` V aTy `App` V a `App` V y )
                 ],
           Pi TyU $ bind aTy $ V aTy --> (Pi nat $ bind x $ tcon "Vec" [V aTy, V x]) ))
    ,
    ("pair", (lam inty $ lam outty $ lam x $ lam y $
              DCon "Tuple" `App`  V inty `App` lam (s2n "_") (V outty) `App` V x `App` V y,
           Pi TyU $ bind inty $ Pi TyU $ bind outty $ V inty -->  (V outty -->  tcon "Sigma" [V inty , lam (s2n "_") $ V outty])))
    ,
    ("first", (lam aTy $ lam p $ lam xy $
                Case [V xy] (ann $ TelBnd Nothing $ u $ NoBnd $ V aTy)
                 [Match $ bind [Pat "Tuple" [PVar $ s2n "_",PVar $ s2n "_",PVar a, PVar $ s2n "_"]] $ V a],
           Pi TyU $ bind aTy $ Pi (V aTy --> TyU) $ bind p $ tcon "Sigma" [V aTy, V p] --> V aTy))

           -- second will not go through without warnings, unless equality without a MUCH omre clever (needs to remember the source of the branch vars from the case, sort of an eta thing)
    -- ,
    -- ("second", (lam aTy $ lam p $ lam xy $ 
    --             Case [V xy] (ann $ 
    --             TelBnd (Just (tcon "Sigma" [V aTy, V p])) -- Nothing 
    --               $ u $ NoBnd $ V p `App` (Ref "first" `App` V aTy `App` V p `App` V xy
    --             ))
    --              [
    --                Match $ bind [Pat "Tuple" [PVar $ s2n "_aTy",PVar $ s2n "_p", PVar $ s2n "_a",PVar b]] $ V b
    --                ],
    --        Pi TyU $ bind aTy $
    --        Pi (V aTy --> TyU) $ bind p $
    --        Pi (tcon "Sigma" [V aTy, V p]) $ bind xy $
    --        (V p `App` (Ref "first" `App` V aTy `App` V p `App` V xy)) ))
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
