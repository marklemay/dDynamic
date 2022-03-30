module Dynamic.Ex2 where
import GHC.Stack


import Dynamic.Ast 
import Dynamic.Norm 
import Dynamic.Err
-- import qualified Dynamic.Env as C --TODO clean
import Dynamic.Env
import Dynamic.Unification
-- import Dynamic.Norm (whnf)
import AlphaShow

import Data.Map (Map)
import qualified Data.Map as Map

import Data.Set (Set)
import qualified Data.Set as Set

import Unbound.Generics.LocallyNameless
import Control.Monad.Except
import Unbound.Generics.LocallyNameless.Unsafe (unsafeUnbind)

import UnboundHelper
import Dynamic.Elab
import Dynamic.Unification
import Control.Lens (Identity(runIdentity))
import Helper
import Prelude hiding (id)
import Dynamic.ElabBase

import PreludeHelper


-- r :: FreshM (WithModuleMT (ExceptT e (WithSourceLocMT Identity)) a)
--   -> Either e a
-- r e = runIdentity $ runWithSourceLocMT' $ runExceptT $ runWithModuleMT (runFreshM e) emptyModule
  -- runWithModuleMT runFreshM (runExceptT (ExceptT e m a) e)
x = s2n "x"
y = s2n "y"
p = s2n "p"
q= s2n "q"

nat = TConF "Nat" [] (NoBnd ()) (NoBnd ())
bool = TConF "Bool" [] (NoBnd ()) (NoBnd ())


vec x = TConF "vec" [x] (NoBnd ()) (TelBnd nat $ u $ NoBnd ())

id a a1 a2 = TConF "Id" [a, a1, a2] (NoBnd ()) (TelBnd TyU $ bind x $ TelBnd (V x) $ u $ TelBnd (V x) $ u $ NoBnd ())

r e =  runIdentity $ runExceptT $ runFreshMT $ runWithModuleMT (runWithSourceLocMT' e ) emptyModule

e1 = r $ fOUni' (empElabInfo pure) $ initProb Set.empty [Equation (Pi TyU $ u $ TyU) TyU TyU (V p)] 
e2 = r $ fOUni' (empElabInfo pure) $ initProb (Set.fromList [x]) [Equation (V x) TyU TyU (V p)]  
e3 = r $ fOUni' (empElabInfo pure) $ initProb (Set.fromList [x]) [Equation (V x) TyU TyU (V p),Equation (V x) (V x)  TyU (V q)]
e4 = r $ fOUni' (empElabInfo pure) $ initProb Set.empty [Equation TyU TyU TyU (V p)]
e5 = r $ fOUni' (empElabInfo pure) $ initProb Set.empty [Equation nat nat TyU (V p)]
e6 = r $ fOUni' (empElabInfo pure) $ initProb (Set.fromList [x,y]) [Equation (vec $ V x) (vec $ V y) TyU (V p)]
e7 = r $ fOUni' (empElabInfo pure) $ initProb (Set.fromList [x,y]) [Equation (id nat (V x) (V x)) (id bool (V y) (V y)) TyU (V p)]

-- pp x = pPrintStringOpt CheckColorTty defaultOutputOptionsDarkBg {outputOptionsCompact = True} x
-- Right let (p,y) = (s2n"p",s2n"y") in 
--   [Equation (V y) (V y) (Union (Tind 0 (V p)) TyU (Tind 0 (V p))) 
--     (Union (Tind 1 (V p)) (Union (Tind 0 (V p)) TyU (Tind 0 (V p))) (Union (Tind 2 (V p)) (Union (Tind 0 (V p)) TyU (Tind 0 (V p))) (V y)))] 
--     fromList [(x, (V y, Tind 0 (V p), Tind 1 (V p)))] [] 
--   [Equation (TConF "Nat" [] (NoBnd ()) (NoBnd ())) (TConF "Bool" [] (NoBnd ()) (NoBnd ())) TyU (Union (TConF "Nat" [] (NoBnd ()) (NoBnd ())) (Union TyU TyU TyU) (Union (Tind 0 (V p)) (Union TyU TyU TyU) (TConF "Bool" [] (NoBnd ()) (NoBnd ()))))]

-- TODO

-- e6 = r $ fOUni' empElabInfo $ initProb (Set.fromList [x]) [Equation (vec $ V x) (vec $ V x) TyU (V p)] 


eqs1 = let (a126,aTy95,aTy125,p_124,x99,y103,_,_1,a) = (s2n"a126",s2n"aTy95",s2n"aTy125",s2n"p_124",s2n"x99",s2n"y103",s2n"_",s2n"_1",s2n"a") in [
  Equation (TConF "Id" [V aTy125, V a126, V a126] (NoBnd ()) (TelBnd TyU (bind a (TelBnd (V a) (u (TelBnd (V a) (bind _1 (NoBnd ())))))))) 
  (App (App (App (TConF "Id" [] (TelBnd TyU (bind a (TelBnd (V a) (u (TelBnd (V a) (bind _1 (NoBnd ()))))))) (TelBnd TyU (bind a (TelBnd (V a) (u (TelBnd (V a) (bind _1 (NoBnd ())))))))) (V aTy95)) (V x99)) (V y103)) TyU (V p_124)]


e80 = let (a126,aTy95,aTy125,p_124,x99,y103,_,_1,a) = (s2n"a126",s2n"aTy95",s2n"aTy125",s2n"p_124",s2n"x99",s2n"y103",s2n"_",s2n"_1",s2n"a") in r $ Dynamic.Norm.whnf (App (App (App (TConF "Id" [] (TelBnd TyU (bind a (TelBnd (V a) (u (TelBnd (V a) (bind _1 (NoBnd ()))))))) (TelBnd TyU (bind a (TelBnd (V a) (u (TelBnd (V a) (bind _1 (NoBnd ())))))))) (V aTy95)) (V x99)) (V y103)) 

prob=let (_,_1,a,a126,aTy95,p_124,x99,y103,aTy125) = (s2n"_",s2n"_1",s2n"a",s2n"a126",s2n"aTy95",s2n"p_124",s2n"x99",s2n"y103",s2n"aTy125") in 
  Prob 
    (Set.fromList [s2n"_",_1,a,aTy95,p_124,x99,y103]) 
    [Equation 
      (C (V x99) (Tind 0 (V p_124))) 
      (V y103) 
      (Tind 0 (V p_124)) 
      (Union (Union (V a126) (Union (Tind 0 (V p_124)) TyU (Tind 0 (V p_124))) (Union (Tind 1 (V p_124)) (Union (Tind 0 (V p_124)) TyU (Tind 0 (V p_124))) (V x99))) (Union (Tind 0 (V p_124)) TyU (Tind 0 (V p_124))) (Union (Union (V a126) (Union (Tind 0 (V p_124)) TyU (Tind 0 (V p_124))) (Union (Tind 2 (V p_124)) (Union (Tind 0 (V p_124)) TyU (Tind 0 (V p_124))) (V y103))) (Union (Tind 0 (V p_124)) TyU (Tind 0 (V p_124))) (V y103)))]
    (Map.fromList [(a126, (V x99, Tind 0 (V p_124), Union (V a126) (Union (Tind 0 (V p_124)) TyU (Tind 0 (V p_124))) (Union (Tind 1 (V p_124)) (Union (Tind 0 (V p_124)) TyU (Tind 0 (V p_124))) (V x99)))),(aTy125, (V aTy95, TyU, Union (Tind 0 (V p_124)) TyU (V aTy95)))] )
    [] 
    []
(x', l, sameTy, why)= let (a126,p_124,x99,y103) = (s2n"a126",s2n"p_124",s2n"x99",s2n"y103") 
  in (y103,
   C (V x99) (Tind 0 (V p_124)),
   Tind 0 (V p_124),
   Union (Union (V a126) (Union (Tind 0 (V p_124)) TyU (Tind 0 (V p_124))) (Union (Tind 1 (V p_124)) (Union (Tind 0 (V p_124)) TyU (Tind 0 (V p_124))) (V x99))) (Union (Tind 0 (V p_124)) TyU (Tind 0 (V p_124))) (Union (Union (V a126) (Union (Tind 0 (V p_124)) TyU (Tind 0 (V p_124))) (Union (Tind 2 (V p_124)) (Union (Tind 0 (V p_124)) TyU (Tind 0 (V p_124))) (V y103))) (Union (Tind 0 (V p_124)) TyU (Tind 0 (V p_124))) (V y103)))

active' = []
e81 = substAddWhyProb x' l Dynamic.Ex2.sameTy Dynamic.Ex2.why $ prob {active= active'}


e8 = r $ fOUni' (empElabInfo Dynamic.Norm.whnf) $ initProb (Set.fromList [s2n"a126",s2n"aTy95",s2n"aTy125",s2n"p_124",s2n"x99",s2n"y103",s2n"_",s2n"_1",s2n"a"]) eqs1

e9 = r $ fOUni' (initElabInfo defualtConfigConfig) $ initProb (Set.fromList [s2n"a126",s2n"aTy95",s2n"aTy125",s2n"p_124",s2n"x99",s2n"y103",s2n"_",s2n"_1",s2n"a"]) eqs1


(flex2,eqs2) = let
    ( aTy26, aTy56, ab57, p_55, x30, y34, _, _1, a,xb53,yb54) =
      ( s2n "aTy26"
      , s2n "aTy56"
      , s2n "ab57"
      , s2n "p_55"
      , s2n "x30"
      , s2n "y34"
      , s2n "_"
      , s2n "_1"
      , s2n "a"
      , s2n "xb53"
      , s2n "yb54"
     ) 
    in
    (Set.fromList
    [ aTy56
    , ab57
    , xb53
    , yb54
    ],
    [ Equation
        ( TConF "Id"
            [ V aTy56
            , V ab57
            , V ab57
            ]
            ( NoBnd () )
            ( TelBnd TyU
                ( bind a
                    ( TelBnd ( V a )
                        ( u
                            ( TelBnd ( V a )
                                ( bind _1
                                    ( NoBnd () )
                                )
                            )
                        )
                    )
                )
            )
        )
        ( App
            ( App
                ( App
                    ( TConF "Id" []
                        ( TelBnd TyU
                            ( bind a
                                ( TelBnd ( V a )
                                    ( u
                                        ( TelBnd ( V a )
                                            ( bind _1
                                                ( NoBnd () )
                                            )
                                        )
                                    )
                                )
                            )
                        )
                        ( TelBnd TyU
                            ( bind a
                                ( TelBnd ( V a )
                                    ( u
                                        ( TelBnd ( V a )
                                            ( bind _1
                                                ( NoBnd () )
                                            )
                                        )
                                    )
                                )
                            )
                        )
                    ) ( V aTy26 )
                ) ( V x30 )
            ) ( V y34 )
        ) TyU ( V p_55 )
    ])


e10 = r $ fOUni' (initElabInfo defualtConfigConfig) $ initProb flex2 eqs2

-- Right let (_,_1,a,a126,aTy95,p_124,x99,y103) = (s2n"_",s2n"_1",s2n"a",s2n"a126",s2n"aTy95",s2n"p_124",s2n"x99",s2n"y103") in 
--   Prob fromList [_,_1,a,aTy95,p_124,x99] [] 
--   fromList [(a126, (V x99, Tind 0 (V p_124), Union (Union (V a126) (Union (Tind 0 (V p_124)) TyU (Tind 0 (V p_124))) (Union (Tind 1 (V p_124)) (Union (Tind 0 (V p_124)) TyU (Tind 0 (V p_124))) (V x99))) (Tind 0 (V p_124)) (V x99))),(aTy125, (V aTy95, TyU, Union (Union (Tind 0 (V p_124)) TyU (V aTy95)) TyU (V aTy95))),(y103, (C (V x99) (Tind 0 (V p_124)), Tind 0 (V p_124), Union (Union (V a126) (Union (Tind 0 (V p_124)) TyU (Tind 0 (V p_124))) (Union (Tind 1 (V p_124)) (Union (Tind 0 (V p_124)) TyU (Tind 0 (V p_124))) (V x99))) (Union (Tind 0 (V p_124)) TyU (Tind 0 (V p_124))) (Union (Union (V a126) (Union (Tind 0 (V p_124)) TyU (Tind 0 (V p_124))) (Union (Tind 2 (V p_124)) (Union (Tind 0 (V p_124)) TyU (Tind 0 (V p_124))) (V y103))) (Union (Tind 0 (V p_124)) TyU (Tind 0 (V p_124))) (V y103))))] [] []
 

ee = let
    ( _, _1, n ) = ( s2n "_", s2n "_1", s2n "n" ) in C
    ( App
        ( DConF "Cons" []
            ( "Vec"
            , TelBnd
                ( TConF "Nat" [] ( NoBnd () ) ( NoBnd () ) )
                ( bind n
                    ( TelBnd
                        ( App
                            ( TConF "Vec" []
                                ( TelBnd
                                    ( TConF "Nat" [] ( NoBnd () ) ( NoBnd () ) )
                                    ( u ( NoBnd () ) )
                                )
                                ( TelBnd
                                    ( TConF "Nat" [] ( NoBnd () ) ( NoBnd () ) )
                                    ( u ( NoBnd () ) )
                                )
                            ) ( V n )
                        )
                        ( u
                            ( NoBnd
                                [ App
                                    ( DConF "S" []
                                        ( "Nat"
                                        , TelBnd
                                            ( TConF "Nat" []
                                                ( NoBnd () )
                                                ( NoBnd () )
                                            )
                                            ( u ( NoBnd [] ) )
                                        )
                                        ( TelBnd
                                            ( TConF "Nat" []
                                                ( NoBnd () )
                                                ( NoBnd () )
                                            )
                                            ( u ( NoBnd () ) )
                                        )
                                        ( NoBnd () )
                                    ) ( V n )
                                ]
                            )
                        )
                    )
                )
            )
            ( TelBnd
                ( TConF "Nat" [] ( NoBnd () ) ( NoBnd () ) )
                ( bind n
                    ( TelBnd
                        ( App
                            ( TConF "Vec" []
                                ( TelBnd
                                    ( TConF "Nat" [] ( NoBnd () ) ( NoBnd () ) )
                                    ( u ( NoBnd () ) )
                                )
                                ( TelBnd
                                    ( TConF "Nat" [] ( NoBnd () ) ( NoBnd () ) )
                                    ( u ( NoBnd () ) )
                                )
                            ) ( V n )
                        )
                        ( u ( NoBnd () ) )
                    )
                )
            )
            ( TelBnd
                ( TConF "Nat" [] ( NoBnd () ) ( NoBnd () ) )
                ( u ( NoBnd () ) )
            )
        )
        ( DConF "Z" [] ( "Nat", NoBnd [] ) ( NoBnd () ) ( NoBnd () ) )
    )
    ( Pi
        ( App
            ( TConF "Vec" []
                ( TelBnd
                    ( TConF "Nat" [] ( NoBnd () ) ( NoBnd () ) )
                    ( u ( NoBnd () ) )
                )
                ( TelBnd
                    ( TConF "Nat" [] ( NoBnd () ) ( NoBnd () ) )
                    ( u ( NoBnd () ) )
                )
            )
            ( Union
                ( DConF "Z" [] ( "Nat", NoBnd [] ) ( NoBnd () ) ( NoBnd () ) )
                ( TConF "Nat" [] ( NoBnd () ) ( NoBnd () ) )
                ( Dind 0
                    ( Tind 0
                        ( TConF "Vec"
                            [ C
                                ( DConF "S"
                                    [ DConF "Z" []
                                        ( "Nat", NoBnd [] )
                                        ( NoBnd () )
                                        ( NoBnd () )
                                    ]
                                    ( "Nat", NoBnd [] )
                                    ( TelBnd
                                        ( TConF "Nat" []
                                            ( NoBnd () )
                                            ( NoBnd () )
                                        )
                                        ( u ( NoBnd () ) )
                                    )
                                    ( NoBnd () )
                                )
                                ( TConF "Nat" [] ( NoBnd () ) ( NoBnd () ) )
                            ]
                            ( NoBnd () )
                            ( TelBnd
                                ( TConF "Nat" [] ( NoBnd () ) ( NoBnd () ) )
                                ( u ( NoBnd () ) )
                            )
                        )
                    )
                )
            )
        )
        ( u
            ( TConF "Vec"
                [ App
                    ( DConF "S" []
                        ( "Nat"
                        , TelBnd
                            ( TConF "Nat" [] ( NoBnd () ) ( NoBnd () ) )
                            ( u ( NoBnd [] ) )
                        )
                        ( TelBnd
                            ( TConF "Nat" [] ( NoBnd () ) ( NoBnd () ) )
                            ( u ( NoBnd () ) )
                        )
                        ( NoBnd () )
                    )
                    ( Union
                        ( DConF "Z" []
                            ( "Nat", NoBnd [] )
                            ( NoBnd () )
                            ( NoBnd () )
                        )
                        ( TConF "Nat" [] ( NoBnd () ) ( NoBnd () ) )
                        ( Dind 0
                            ( Tind 0
                                ( TConF "Vec"
                                    [ C
                                        ( DConF "S"
                                            [ DConF "Z" []
                                                ( "Nat", NoBnd [] )
                                                ( NoBnd () )
                                                ( NoBnd () )
                                            ]
                                            ( "Nat", NoBnd [] )
                                            ( TelBnd
                                                ( TConF "Nat" []
                                                    ( NoBnd () )
                                                    ( NoBnd () )
                                                )
                                                ( u ( NoBnd () ) )
                                            )
                                            ( NoBnd () )
                                        )
                                        ( TConF "Nat" []
                                            ( NoBnd () )
                                            ( NoBnd () )
                                        )
                                    ]
                                    ( NoBnd () )
                                    ( TelBnd
                                        ( TConF "Nat" []
                                            ( NoBnd () )
                                            ( NoBnd () )
                                        )
                                        ( u ( NoBnd () ) )
                                    )
                                )
                            )
                        )
                    )
                ]
                ( NoBnd () )
                ( TelBnd
                    ( TConF "Nat" [] ( NoBnd () ) ( NoBnd () ) )
                    ( u ( NoBnd () ) )
                )
            )
        )
    )
