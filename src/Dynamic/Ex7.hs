module Dynamic.Ex7 where


import Dynamic.Ast 
import Dynamic.Norm ( isValue, whnf ) 
import Dynamic.Err
-- import qualified Dynamic.Env as C --TODO clean=
import Dynamic.Unification
-- import Dynamic.Norm (whnf)
import AlphaShow

import Data.Map (Map)
import qualified Data.Map as Map

import Data.Set (Set)
import qualified Data.Set as Set

import Unbound.Generics.LocallyNameless
import UnboundHelper
import PreludeHelper
import Dynamic.Eq
import Dynamic.Env
import Dynamic.TestEnv (stdModule)


-- eqDef
( aA, wild, _1, x ) = ( s2n "A", s2n "_", s2n "_1", s2n "x" ) 
l = TConF "Id"
    [ Pi
        ( TConF "Bool" [] ( NoBnd () ) ( NoBnd () ) )
        ( u ( TConF "Bool" [] ( NoBnd () ) ( NoBnd () ) ) )
    , Fun
        ( bind
            ( wild, x )
            ( DConF "t" [] ( "Bool", NoBnd [] ) ( NoBnd () ) ( NoBnd () ) )
        )
    , Fun
        ( bind
            ( wild, x )
            ( DConF "t" [] ( "Bool", NoBnd [] ) ( NoBnd () ) ( NoBnd () ) )
        )
    ]
    ( NoBnd () )
    ( TelBnd TyU
        ( bind aA
            ( TelBnd ( V aA )
                ( u ( TelBnd ( V aA ) ( u ( NoBnd () ) ) ) )
            )
        )
    )
r = App
    ( App
        ( App
            ( TConF "Id" []
                ( TelBnd TyU
                    ( bind aA
                        ( TelBnd ( V aA )
                            ( u
                                ( TelBnd ( V aA ) ( u ( NoBnd () ) ) )
                            )
                        )
                    )
                )
                ( TelBnd TyU
                    ( bind aA
                        ( TelBnd ( V aA )
                            ( u
                                ( TelBnd ( V aA ) ( u ( NoBnd () ) ) )
                            )
                        )
                    )
                )
            )
            ( Pi
                ( TConF "Bool" [] ( NoBnd () ) ( NoBnd () ) )
                ( u ( TConF "Bool" [] ( NoBnd () ) ( NoBnd () ) ) )
            )
        )
        ( Fun
            ( bind
                ( wild, x )
                ( DConF "f" []
                    ( "Bool", NoBnd [] )
                    ( NoBnd () )
                    ( NoBnd () )
                )
            )
        )
    )
    ( Fun
        ( bind
            ( wild, x )
            ( DConF "f" [] ( "Bool", NoBnd [] ) ( NoBnd () ) ( NoBnd () ) )
        )
    )

rr e = runFreshM $ runWithModuleMT e stdModule
ee  = rr $ eqDef l dummyInfo TyU r