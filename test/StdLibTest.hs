{-# LANGUAGE FlexibleContexts #-}
module StdLibTest where

import Prelude hiding (head)

import Test.Tasty (testGroup)
import Test.Tasty.HUnit (Assertion(..), assertEqual, assertBool, testCase)
import Test.Tasty.QuickCheck (testProperty)


import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless.Name
import Unbound.Generics.LocallyNameless.Bind
import GHC.Generics (Generic)
import Data.Typeable (Typeable)

import Data.Map (Map)
import qualified Data.Map as Map

import Ast
import Helper
import UnboundHelper
import Env
import Norm
import Eq
import Ty

import StdLib
import Control.Monad.Except (MonadError)

import Data.Either


stdLibTest = testGroup "StdLibTest tests" [
  testCase "" $ assertEqual "wf stdlib" (Right ()) $ runTcMonad stdlib envWf,
  testCase "" $ assertEqual "safeWhnf doesn't run forever" (Right $ (Fun $ bind (f, x) $ V f `App` V x) `App` n 0) $ runTcMonad empctx $ safeWhnf $ (Fun $ bind (f, x) $ V f `App` V x) `App` n 0,
  
  testCase "" $ assertEqual "whnf to 0" (Right $ n 0) $ runTcMonad stdlib $ whnf $ annonoToZero `App` n 3,
  testCase "" $ assertEqual "eval to 0" (Right $ n 0) $ runTcMonad stdlib $ eval $ annonoToZero `App` n 3,
  testCase "" $ assertStdInfer "annonoToZero" $ annonoToZero, -- TODO reactivate when simple inference on the motive is avialible

  testCase "" $ assertEqual "local definition of Cong" (Right $ (Pi TyU $ bind inty $ Pi TyU $ bind outty $ Pi (V inty) $ bind x $ Pi (V inty) $ bind y $ (tcon "Id" [V inty, V x, V y]) --> ( Pi (V inty --> V outty) $ bind f $ tcon "Id" [V outty, V f `App` V x, V f `App` V y]))) $ fmap snd $ runTcMonad stdlib $ tyInfer annoCong,

  testCase "" $ assertEqual "local definition of transitivity typchecks" (Right $ (Pi TyU $ bind aTy $ Pi (V aTy) $ bind x $Pi (V aTy) $ bind y $ tcon "Id" [V aTy, V x, V y] --> (Pi (V aTy) $ bind z $ tcon "Id" [V aTy, V y, V z] -->  tcon "Id" [V aTy, V x, V z]))) $ fmap snd $ runTcMonad stdlib $ tyInfer annoTrans,

  testCase "" $ assertEqual "tt = tt" (Right TyU) $ fmap snd $ runTcMonad stdlib $ tyInfer $ tcon "Id" [unit, DCon "tt", DCon "tt"],
  testCase "" $ assertEqual "tt = tt" (Right $tcon "Id" [unit, DCon "tt", DCon "tt"]) $ fmap snd $ runTcMonad stdlib $ tyInfer $ DCon "Refl" `apps` [unit, DCon "tt"],

  testCase "" $ assertEqual "local def of first" (Right $ Pi TyU $ bind aTy $ Pi (V aTy --> TyU) $ bind p $ tcon "Sigma" [V aTy, V p ] --> V aTy) $ fmap snd $ runTcMonad stdlib $ tyInfer annofst,
  testCase "" $ assertEqual "local def of snd" (Right $ Pi TyU $ bind aTy $ Pi (V aTy --> TyU) $ bind p $ Pi (tcon "Sigma" [V aTy, V p]) $ bind xy $ (V p `App` (V first `App` V aTy `App` V p `App` V xy))) $ fmap snd $ runTcMonad stdlib $ tyInfer annosnd,
  testCase "" $ assertEqual "non-dependent pair" (Right $ Pi TyU $ bind inty $ Pi TyU $ bind outty $ V inty -->  (V outty -->  tcon "Sigma" [V inty , lam (s2n "_") $ V outty])) $ fmap snd $ runTcMonad stdlib $ tyInfer annopair,


-- claims hard in https://repository.upenn.edu/edissertations/1137/ ?
  testCase "" $ assertStdInfer "addition is associative" $
  (Fun $ bind (ih , x) $ lam y $ lam z $
  Case (V x) (ann $ bind (x,[]) $ tcon "Id" [nat, V add `App` V x `App` (V add `App` V y `App` V z), V add `App` (V add `App` V x `App` V y) `App` V z]) [
                  Match "Z" $ bind []   $ DCon "Refl" `apps` [nat, (V add `App` V y `App` V z)],
                  Match "S" $ bind [xx] $  V cong `apps` [nat, nat,
                   V add `App` V xx `App` (V add `App` V y `App` V z) ,
                   V add `App` (V add `App` V xx `App` V y) `App` V z ,
                   V ih `apps` [V xx, V y, V z],
                   DCon "S" ]
                  ]
   ) ::: (Pi nat $ bind x $ Pi nat $ bind y $ Pi nat $ bind z $ tcon "Id" [nat, V add `App` V x `App` (V add `App` V y `App` V z), V add `App` (V add `App` V x `App` V y) `App` V z]),

 testCase "" $ assertEqual "singleton true" (Right $ tcon "Sing" [tcon "Bool" [], DCon "true"]) $ fmap snd $ runTcMonad stdlib $ tyInfer singTrue,
 testCase "" $ assertStdInfer "the dynamic challenge wf" $  dynamicChallengrTy ::: TyU,
 testCase "" $ assertStdInfer "the dynamic challenge typechecks" $ dynamicChallengeex ::: dynamicChallengrTy,

 testCase "" $ assertStdInfer "singUniqueEx 1" $ 
  singUniqueEx :::
  (
  Pi TyU $ bind aTy $ Pi (V aTy) $ bind a $ 
  Pi (tcon "Sing" [V aTy, V a]) $ bind x $ Pi (tcon "Sing" [V aTy, V a]) $ bind y $
  tcon "Id" [tcon "Sing" [V aTy, V a], V x, V y]
  ),

 testCase "" $ assertStdInfer "singUniqueEx ty wf" $ ( (
  Pi TyU $ bind aTy $ Pi (V aTy) $ bind a $ 
  Pi (tcon "Sing" [V aTy, V a]) $ bind x $ Pi (tcon "Sing" [V aTy, V a]) $ bind y $
  tcon "Id" [tcon "Sing" [V aTy, V a], V x, V y]
  ) ::: TyU),


 testCase "" $ assertStdInfer "all units" $ allunitsEqEx ::: (Pi unit $ bind x $ Pi unit $ bind y $ tcon "Id" [unit, V x, V y]),
 testCase "" $ assertStdInfer "all units ty wf" $ (Pi unit $ bind x $ Pi unit $ bind y $ tcon "Id" [unit, V x, V y]) ::: TyU,

 testCase "" $ assertEqual "eval allunitsEqEx" (Right $ ((DCon "Refl") `App` (tcon "Unit" [])) `App` (DCon "tt")) $ runTcMonad stdlib $ eval ( allunitsEqEx `apps` [tt, tt]),

 testCase "" $ assertEqual "3 element vector" (Right $ tcon "Vec" [nat, n 3]) $ fmap snd $ runTcMonad stdlib $ tyInfer $ ls [n 1, n 3, n 5] nat,


 testCase "" $ assertStdInfer "annorep" annorep,
 testCase "" $ assertEqual "eval annorep" (Right (ls [(DCon "tt"),(DCon "tt"),(DCon "tt"),(DCon "tt"),(DCon "tt")] (tcon "Unit" []) )) $ runTcMonad stdlib $ eval $ annorep `App` tcon "Unit" [] `App` DCon "tt" `App` n 5,


 testCase "" $ assertStdInfer "annoSym" annoSym,
 
 testCase "" $ assertEqual "annoSym eval" (Right $ ((DCon "Refl") `App` nat) `App` (n 1)) $ runTcMonad stdlib $ eval $ annoSym `App` nat `App` n 1 `App` n 1 `App` (DCon "Refl" `App` nat `App` n 1),
 
 testCase "" $ assertEqual "3 element vector" (Right $ n 5) $ runTcMonad stdlib $ eval $ V add `App` n 3 `App` n 2,

 
 testCase "" $ assertEqual "anno add" (Right $ n 7) $ runTcMonad stdlib $ eval $ annonoAdd `App` n 3 `App` n 4,
 testCase "" $ assertStdInfer "anno add" annonoAdd,

 testCase "" $ assertStdInfer "exp0isx" exp0isx,
 testCase "" $ assertStdInfer "addsuc" addsuc,
 testCase "" $ assertStdInfer "addcom" addcom,

 
 testCase "" $ assertStdInfer "addcom" lightHead,
 testCase "" $ assertStdInfer "addcom" $ V head  `apps` [nat, n 2, ls [n 9, n 8,n 7] nat ],
 testCase "" $ assertStdInfer "addcom" $ lightHead  `apps` [nat, n 2, ls [n 9, n 8,n 7] nat ],
 testCase "" $ assertEqual "head evals correctly" (Right $ n 9) $ runTcMonad stdlib $ eval $  V head `apps` [nat, n 2, ls [n 9, n 8,n 7] nat ],
 testCase "" $ assertEqual "head evals correctly" (Right $ n 9) $ runTcMonad stdlib $ eval $  lightHead `apps` [nat, n 2, ls [n 9, n 8,n 7] nat ],

 testCase "" $ assertStdInfer "head tychecks under binder" $ (lam x $ (V head) `apps` [nat, V x, (V rep) `apps` [nat, n 7, s $ V x]]) ::: (nat --> nat),-- (Right $ n 9) $ runTcMonad stdlib $ eval $  lightHead `apps` [nat, n 2, ls [n 9, n 8,n 7] nat ]
 testCase "" $ assertStdInfer "head tychecks under binder" $ (lam x $ lightHead `apps` [nat, V x, (V rep) `apps` [nat, n 7, s $ V x]]) ::: (nat --> nat),

 testCase "" $ assertStdInfer "head tychecks under binder via left addition" $ (lam x $ (V head) `apps` [nat, V x, (V rep) `apps` [nat, n 7, V add `apps` [n 1, V x]]]) ::: (nat --> nat),-- (Right $ n 9) $ runTcMonad stdlib $ eval $  lightHead `apps` [nat, n 2, ls [n 9, n 8,n 7] nat ]
 testCase "" $ assertStdInfer "head tychecks under binder via left addition" $ (lam x $ lightHead `apps` [nat, V x, (V rep) `apps` [nat, n 7,  V add `apps` [n 1, V x]]]) ::: (nat --> nat),
-- famously  V add `apps` [V x, n 1] will not work

 testCase "" $ assertEqual "head evals correctly" (Right $ n 7) $ runTcMonad stdlib $ eval $  ( (lam x $ lightHead `apps` [nat, V x, (V rep) `apps` [nat, n 7,  V add `apps` [n 1, V x]]]) ::: (nat --> nat) ) `App` n 3
  ]

lightHead =  (lam outty $ lam x $ lam y $ Case (V y) (An $ Just $ bind (unnamed, [aTy', unnamed]) $ V aTy') [-- TODO seems like this should be infferable withotu the annotation
   Match "Nil" $ bind [aTy] $ Solve noAn,
   Match "Cons" $ bind [aTy,a,x,xx] $ V a
 ]
 ) :::  (Pi TyU $ bind outty $ Pi nat $ bind x $ Pi (tcon "Vec" [V outty, s $ V x]) $ u $ V outty)


assertStdInfer s e = assertBool s $ isRight $ runTcMonad stdlib $ tyInfer e -- TODO also check well formedness

-- some reusable expressions
-- TODO: move the addition stuff to another test

exp0isx = (Fun $ bind (f, x) $
  Case (V x) (An $ Just $ bind (xx,[]) $  tcon "Id" [nat, V xx, V add `apps` [V xx, n 0]]) [
    Match "Z" $ bind []   $  DCon "Refl" `apps` [nat, n 0],
    Match "S" $ bind [xx] $  V cong `apps` [nat, nat, V xx, V add `apps` [V xx, n 0], V f `App` V xx , DCon "S" ]
  ] )
  ::: (Pi nat $ bind x $ tcon "Id" [nat, V x, V add `apps` [V x, n 0]] )



addsuc = (Fun $ bind (f, x) $ lam y $ 
  Case (V x) (An $ Just $ bind (xx,[]) $ tcon "Id" [nat,  DCon "S" `App` (V add `apps` [V xx, V y]) , V add `apps` [V xx, DCon "S" `App` V y]] 
  ) [
    Match "Z" $ bind []   $ DCon "Refl" `apps` [nat, DCon "S" `App` (V add `apps` [n 0, V y]) ],
    Match "S" $ bind [xx] $  V cong `apps` [nat, nat, 
      DCon "S" `App` (V add `apps` [V xx, V y]), 
      V add `apps` [V xx, DCon "S" `App` V y], 
      V f `apps` [V xx, V y],
      DCon "S" ]
  ]
   )
  ::: (Pi nat $ bind x $ Pi nat $ bind y $ tcon "Id" [nat,  DCon "S" `App` (V add `apps` [V x, V y]) , V add `apps` [V x, DCon "S" `App` V y]] )


addcom = (Fun $ bind (f, x) $ lam y $
  Case (V x) (An $ Just $ bind (xx,[]) $ tcon "Id" [nat, V add `apps` [V xx, V y], V add `apps` [V y, V xx]]  ) [
    Match "Z" $ bind []   $ exp0isx `App` (V add `apps` [n 0, V y]),
    Match "S" $ bind [xx] $ V trans `apps` [nat, 
      DCon "S"  `App` (V add `apps` [V xx, V y]),
      DCon "S"  `App` (V add `apps` [V y, V xx]),
       V cong `apps` [nat, nat, 
       V add `apps` [V xx, V y],
       V add `apps` [V y, V xx],
       V f `apps` [V xx, V y],
       DCon "S"
       ],
      V add `apps` [V y, DCon "S" `App` V xx],
      addsuc `apps` [V y, V xx]
      ]
  ]) :::  (Pi nat $ bind x $ Pi nat $ bind y $ tcon "Id" [nat, V add `apps` [V x, V y], V add `apps` [V y, V x]] )
  



annonoAdd = let
  add = s2n "add"
  x = s2n "x"
  y = s2n "y"
  x' = s2n "x'"
  in (Fun $ bind (add, x) $ lam y $ Case (V x) (ann $ bind (s2n "_",[]) nat) [
    Match "Z" $ bind []   $ V y,
    Match "S" $ bind [x'] $ s $ V add `App` V x' `App` V y]) ::: (nat --> (nat --> nat))


ex1 = runTcMonad stdlib $ whnf $ annonoAdd `App` n 3 `App` n 4 --TODO 
ex11 = runTcMonad stdlib $ safeWhnf $ annonoAdd `App` n 3 `App` n 4 --TODO 









annoSym = (lam aTy $ lam x $ lam y $ lam xy $ 
  Case (V xy) (ann $ bind (s2n "_",[aTy,x,y]) $ tcon "Id" [V aTy, V y, V x])
  [Match "Refl" $ bind [aTy,a] $ DCon "Refl" `App` V aTy `App` V a]
  ) ::: (Pi TyU $ bind aTy $ Pi (V aTy) $ bind x $ Pi (V aTy) $ bind y $ tcon "Id" [V aTy, V x, V y] --> tcon "Id" [V aTy, V y, V x])



exbuiltinAdd0 = runTcMonad stdlib $ whnf $ V add `App` n 3 `App` n 2 --TODO add at somepoint



annorep = (Fun $ bind (rep, aTy) $ lam a $ lam x $ 
              Case (V x) (ann $ bind (x,[]) $ tcon "Vec" [V aTy, V x])
                [Match "Z" $ bind []  $ DCon "Nil" `App` V aTy,
                 Match "S" $ bind [y] $  DCon "Cons" `App` V aTy `App` V a `App` V y `App` (V rep `App` V aTy `App` V a `App` V y )]
  ) ::: (Pi TyU $ bind aTy $ V aTy --> (Pi nat $ bind x $ tcon "Vec" [V aTy, V x]) )

allunitsEqEx = lam x $ lam y $ 
  Case (V x) (ann $ bind (xx,[]) $ tcon "Id" [unit, V xx, V y])
    [Match "tt" $ bind [] $ 
  Case (V y) (ann $ bind (yy,[]) $ tcon "Id" [unit, tt, V yy])
    [Match "tt" $ bind [] $ DCon "Refl" `apps` [unit, tt]]
  ]










singTrue = DCon "mkSing" `apps` [tcon "Bool" [], DCon "true"]

singTrueTy =  tcon "Sing" [tcon "Bool" [], DCon "true"]

dynamicChallengeLongex = lam x $ lam y $ lam f $ V cong `apps` [singTrueTy, bool, V x, V y, singUniqueEx `apps` [bool, DCon "true", V x, V y], V f] --TODO: chop f
dynamicChallengeex = (lam x $ lam y $  V cong `apps` [singTrueTy, bool, V x, V y, singUniqueEx `apps` [bool, DCon "true", V x, V y]]) ::: dynamicChallengrTy --TODO: chop f


dynamicChallengrTy = Pi singTrueTy $ bind x $ Pi singTrueTy $ bind y $ Pi (singTrueTy --> bool) $ bind f $ 
  -- (tcon "Id" [singTrueTy, V x, V y]) --> ( Pi (singTrueTy --> bool) $ bind f $ tcon "Id" [bool, V f `App` V x, V f `App` V y])
  tcon "Id" [bool, V f `App` V x, V f `App` V y]

-- TODO add to testing when auto casting is supported
dynamicChallengrevaltt = runTcMonad stdlib $ eval (dynamicChallengeex `apps` [singTrue,singTrue])
dynamicChallengrevaltf = runTcMonad stdlib $ eval (dynamicChallengeex `apps` [DCon "mkSing" `apps` [tcon "Bool" [], DCon "true"], DCon "mkSing" `apps` [tcon "Bool" [], DCon "false"]])
dynamicChallengrevalft = runTcMonad stdlib $ eval (dynamicChallengeex `apps` [DCon "mkSing" `apps` [tcon "Bool" [], DCon "false"], DCon "mkSing" `apps` [tcon "Bool" [], DCon "true"]])
dynamicChallengrevaff = runTcMonad stdlib $ eval (dynamicChallengeex `apps` [DCon "mkSing" `apps` [tcon "Bool" [], DCon "false"], DCon "mkSing" `apps` [tcon "Bool" [], DCon "false"]])



singUniqueEx :: Exp
singUniqueEx = (
  lam aTy $ lam a $ 
  lam x $
     Case (V x) (ann $ bind (xx, [aTy', a']) $ Pi (tcon "Sing" [V aTy', V a']) $ bind (y) $ tcon "Id" [tcon "Sing" [V aTy', V a'], V xx, V y] )
    [Match "mkSing" $ bind [aTy, a] $ 
     lam y $ 
    Case (V y) (ann $ bind (yy, [aTy', a']) $ tcon "Id" [tcon "Sing" [V aTy', V a'], DCon "mkSing" `apps` [V aTy', V a'], V yy] )
    [Match "mkSing" $ bind [aTy', a'] $ DCon "Refl" `apps` [tcon "Sing" [V aTy', V a'],  DCon "mkSing" `apps` [V aTy', V a']]]
  ]) :::
  (
  Pi TyU $ bind aTy $ Pi (V aTy) $ bind a $ 
  Pi (tcon "Sing" [V aTy, V a]) $ bind x $ Pi (tcon "Sing" [V aTy, V a]) $ bind y $
  tcon "Id" [tcon "Sing" [V aTy, V a], V x, V y]
  )

annofst = (lam aTy $ lam p $ lam xy $
                Case (V xy) (ann $ bind (s2n "_", [aTy, p]) $ V aTy)
                [Match "Tuple" $ bind [s2n "_",s2n "_",a, s2n "_"] $ V a]
  ) ::: (Pi TyU $ bind aTy $ Pi (V aTy --> TyU) $ bind p $ tcon "Sigma" [V aTy, V p ] --> V aTy)

annosnd = (lam aTy $ lam p $ lam xy $ 
                Case (V xy) (ann $ bind (xy, [aTy, p]) $ V p `App` (V first `App` V aTy `App` V p `App` V xy))
                [Match "Tuple" $ bind [s2n "_",s2n "_",s2n "_", b] $ V b]
  ) ::: (Pi TyU $ bind aTy $ Pi (V aTy --> TyU) $ bind p $ Pi (tcon "Sigma" [V aTy, V p]) $ bind xy $ (V p `App` (V first `App` V aTy `App` V p `App` V xy)))

annopair = (lam inty $ lam outty $ lam x $ lam y $
              DCon "Tuple" `App`  V inty `App` (lam (s2n "_") $ V outty) `App` V x `App` V y
  ) ::: (Pi TyU $ bind inty $ Pi TyU $ bind outty $ V inty -->  (V outty -->  tcon "Sigma" [V inty , lam (s2n "_") $ V outty]))


-- this formulation needs a different cong?
annoCong = (lam inty $ lam outty $ lam x $ lam y $ lam xy $
              Case (V xy) (ann $ bind (s2n "_", [inty, x,y]) $ Pi (V inty --> V outty) $ bind f $  tcon "Id" [V outty, V f `App` V x, V f `App` V y])
                [Match "Refl" $ bind [s2n "_", a] $  lam f $ DCon "Refl" `App`  V outty `App` (V f `App` V a) ]
  ) ::: (Pi TyU $ bind inty $ Pi TyU $ bind outty $ Pi (V inty) $ bind x $ Pi (V inty) $ bind y $ (tcon "Id" [V inty, V x, V y]) --> ( Pi (V inty --> V outty) $ bind f $ tcon "Id" [V outty, V f `App` V x, V f `App` V y]))
  


annoTrans = (lam aTy $ lam x $ lam y $ lam xy $
               Case (V xy) (ann $ bind (s2n "_", [aTy,a,a']) $  (Pi (V aTy) $ bind z $ tcon "Id" [V aTy, V a', V z] -->  tcon "Id" [V aTy, V a, V z]))
                 [Match "Refl" $ bind [aTy,a] $ lam (s2n "_") $ lam az $ V az]
  ) ::: (Pi TyU $ bind aTy $ Pi (V aTy) $ bind x $Pi (V aTy) $ bind y $ tcon "Id" [V aTy, V x, V y] --> (Pi (V aTy) $ bind z $ tcon "Id" [V aTy, V y, V z] -->  tcon "Id" [V aTy, V x, V z]))


annonoToZero = let
  tozero = s2n "tozero"
  x = s2n "x"
  x' = s2n "x'"
  in (Fun $ bind (tozero, x) $ Case (V x) noAn [
    Match "Z" $ bind []  $ n 0,
    Match "S" $ bind [x'] $ V tozero `App` V x']) ::: (nat --> nat)




recbegindSuc = let
  recc = s2n "recc"
  x = s2n "x"
  y = s2n "y"
  x' = s2n "x'"
  in Fun $ bind (recc, x) $ DCon "S" `App` (V recc `App` V x')

ex0 = runTcMonad stdlib $ whnf $ recbegindSuc `App` n 0 -- TODO test eventually


-- TODO: need something like this to properly test WHNF without over specifiing behavour
-- "first order" unification
assertUnifiesWith :: (Bind [Var] Exp) -> Exp -> Assertion
assertUnifiesWith = undefined


-- TODO: var ctx, TODO: unification ctx?
unifiesWith' :: (MonadError String m) => Exp -> Exp -> Map Var Exp ->  m (Map Var Exp)
unifiesWith' (V l) (V r) defs | l `aeq` r = pure defs
unifiesWith' (V l) r defs = case Map.lookup l defs of
  Just def -> unifiesWith' def r defs
  Nothing -> pure $ Map.insert l r defs 
unifiesWith' (trml ::: tyl) (trmr ::: tyr) defs = do
  defs' <- unifiesWith' trml trmr defs
  unifiesWith' tyl tyr defs'
-- ...


--local names
a = s2n "a"
a' = s2n "a'"
aTy = s2n "aTy"
b = s2n "b"
x = s2n "x"
y = s2n "y"
z = s2n "z"
xy = s2n "xy"
yz = s2n "yz"
az = s2n "az"
inty = s2n "inty"
outty = s2n "outty"
p = s2n "p"
first = s2n "first"
f = s2n "f"
ih = s2n "ih"
xx = s2n "xx"
yy = s2n "yy"
aTy' = s2n "aTy'"