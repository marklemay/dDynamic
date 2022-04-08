module Dynamic.Ex8 where


import Dynamic.Ast 
import Dynamic.Norm ( isValue, whnf, cbvErrNext, cbvOrErr ) 
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
import Prelude hiding (exp)
import Data.Functor.Identity
import Control.Monad.Except



rr e = runIdentity $ runExceptT $ runFreshMT $ runWithModuleMT ( e) stdModule
e0 = rr $ cbvOrErr exp

e1 = rr $ do e <- cbvOrErr exp; cbvOrErr e


e2' = rr $ cbvOrErr e2


e3' = rr $ cbvOrErr e3 -- here is prob

e3'' = rr $ do e <- cbvOrErr e3; cbvOrErr e

e4' = rr $ cbvOrErr e4 -- here is prob!

e5' = rr $ cbvOrErr e5 -- here is prob!!!

e5 =    ( Union
        ( TConF "Bool" [] ( NoBnd () ) ( NoBnd () ) ) TyU
        ( Union
            ( Union
                ( Same
                    ( TConF "Bool" [] ( NoBnd () ) ( NoBnd () ) ) 
                    dummyInfo
                    TyU
                    ( TConF "Bool" [] ( NoBnd () ) ( NoBnd () ) )
                ) TyU
                ( TConF "Bool" [] ( NoBnd () ) ( NoBnd () ) )
            ) TyU
            ( TConF "Bool" [] ( NoBnd () ) ( NoBnd () ) )
        )
    )


e4 =App
    ( C
        ( Fun
            ( bind
                ( w_, x )
                ( DConF "true" []  ( "Bool", NoBnd [] ) ( NoBnd () ) ( NoBnd () )
                )
            )
        )
        ( Union
            ( Pi
                ( TConF "Bool" [] ( NoBnd () ) ( NoBnd () ) )
                ( bind w_ ( TConF "Bool" [] ( NoBnd () ) ( NoBnd () ) ) )
            ) TyU
            ( Union
                ( Union
                    ( Tind 0
                        ( TConF "Id"
                            [ Pi ( Same
                                    ( TConF "Bool" []
                                        ( NoBnd () )
                                        ( NoBnd () )
                                    ) dummyInfo TyU
                                    ( TConF "Bool" []
                                        ( NoBnd () )
                                        ( NoBnd () )
                                    ) )
                                ( bind w_
                                    ( Same
                                        ( TConF "Bool" []
                                            ( NoBnd () )
                                            ( NoBnd () )
                                        ) dummyInfo TyU
                                        ( TConF "Bool" []
                                            ( NoBnd () )
                                            ( NoBnd () )
                                        )
                                    )
                                )
                            , Same
                                ( Fun
                                    ( bind
                                        ( w_, x )
                                        ( DConF "true" []
                                            ( "Bool", NoBnd [] )
                                            ( NoBnd () )
                                            ( NoBnd () )
                                        )
                                    )
                                ) dummyInfo
                                ( Pi
                                    ( Same
                                        ( TConF "Bool" []
                                            ( NoBnd () )
                                            ( NoBnd () )
                                        ) dummyInfo TyU
                                        ( TConF "Bool" []
                                            ( NoBnd () )
                                            ( NoBnd () )
                                        )
                                    )
                                    ( bind w_
                                        ( Same
                                            ( TConF "Bool" []
                                                ( NoBnd () )
                                                ( NoBnd () )
                                            ) dummyInfo TyU
                                            ( TConF "Bool" []
                                                ( NoBnd () )
                                                ( NoBnd () )
                                            )
                                        )
                                    )
                                )
                                ( Fun
                                    ( bind
                                        ( w_, x )
                                        ( DConF "true" []
                                            ( "Bool", NoBnd [] )
                                            ( NoBnd () )
                                            ( NoBnd () )
                                        )
                                    )
                                )
                            , Same
                                ( Fun
                                    ( bind
                                        ( w_, x )
                                        ( DConF "true" []
                                            ( "Bool", NoBnd [] )
                                            ( NoBnd () )
                                            ( NoBnd () )
                                        )
                                    )
                                ) dummyInfo
                                ( Pi
                                    ( Same
                                        ( TConF "Bool" []
                                            ( NoBnd () )
                                            ( NoBnd () )
                                        ) dummyInfo TyU
                                        ( TConF "Bool" []
                                            ( NoBnd () )
                                            ( NoBnd () )
                                        )
                                    )
                                    ( bind w_
                                        ( Same
                                            ( TConF "Bool" []
                                                ( NoBnd () )
                                                ( NoBnd () )
                                            ) dummyInfo TyU
                                            ( TConF "Bool" []
                                                ( NoBnd () )
                                                ( NoBnd () )
                                            )
                                        )
                                    )
                                )
                                ( Fun
                                    ( bind
                                        ( w_, x )
                                        ( DConF "false" []
                                            ( "Bool", NoBnd [] )
                                            ( NoBnd () )
                                            ( NoBnd () )
                                        )
                                    )
                                )
                            ]
                            ( NoBnd () )
                            ( TelBnd TyU
                                ( bind aA
                                    ( TelBnd ( V aA )
                                        ( bind w_
                                            ( TelBnd ( V aA )
                                                ( bind _1 ( NoBnd () ) )
                                            )
                                        )
                                    )
                                )
                            )
                        )
                    ) TyU
                    ( Pi
                        ( TConF "Bool" [] ( NoBnd () ) ( NoBnd () ) )
                        ( bind _3
                            ( TConF "Bool" [] ( NoBnd () ) ( NoBnd () ) )
                        )
                    )
                ) TyU
                ( Pi
                    ( TConF "Bool" [] ( NoBnd () ) ( NoBnd () ) )
                    ( bind _3 ( TConF "Bool" [] ( NoBnd () ) ( NoBnd () ) ) )
                )
            )
        )
    )
    ( DConF "true" [] ( "Bool", NoBnd [] ) ( NoBnd () ) ( NoBnd () ) )



e3 = ( App e2 ( App
                        ( C
                            ( Fun
                                ( bind
                                    ( w_, x )
                                    ( DConF "true" []
                                        ( "Bool", NoBnd [] )
                                        ( NoBnd () )
                                        ( NoBnd () )
                                    )
                                )
                            )
                            ( Union
                                ( Pi
                                    ( TConF "Bool" []
                                        ( NoBnd () )
                                        ( NoBnd () )
                                    )
                                    ( bind w_
                                        ( TConF "Bool" []
                                            ( NoBnd () )
                                            ( NoBnd () )
                                        )
                                    )
                                ) TyU
                                ( Union
                                    ( Union
                                        ( Tind 0
                                            ( TConF "Id"
                                                [ Pi
                                                    ( Same
                                                        ( TConF "Bool" []
                                                            ( NoBnd () )
                                                            ( NoBnd () )
                                                        ) dummyInfo TyU
                                                        ( TConF "Bool" []
                                                            ( NoBnd () )
                                                            ( NoBnd () )
                                                        )
                                                    )
                                                    ( bind w_
                                                        ( Same
                                                            ( TConF "Bool" []
                                                                ( NoBnd () )
                                                                ( NoBnd () )
                                                            ) dummyInfo TyU
                                                            ( TConF "Bool" []
                                                                ( NoBnd () )
                                                                ( NoBnd () )
                                                            )
                                                        )
                                                    )
                                                , Same
                                                    ( Fun
                                                        ( bind
                                                            ( w_, x )
                                                            ( DConF "true" []
                                                                ( "Bool"
                                                                , NoBnd []
                                                                )
                                                                ( NoBnd () )
                                                                ( NoBnd () )
                                                            )
                                                        )
                                                    ) dummyInfo
                                                    ( Pi
                                                        ( Same
                                                            ( TConF "Bool" []
                                                                ( NoBnd () )
                                                                ( NoBnd () )
                                                            ) dummyInfo TyU
                                                            ( TConF "Bool" []
                                                                ( NoBnd () )
                                                                ( NoBnd () )
                                                            )
                                                        )
                                                        ( bind w_
                                                            ( Same
                                                                ( TConF "Bool" []
                                                                    ( NoBnd () )
                                                                    ( NoBnd () )
                                                                ) dummyInfo TyU
                                                                ( TConF "Bool" []
                                                                    ( NoBnd () )
                                                                    ( NoBnd () )
                                                                )
                                                            )
                                                        )
                                                    )
                                                    ( Fun
                                                        ( bind
                                                            ( w_, x )
                                                            ( DConF "true" []
                                                                ( "Bool"
                                                                , NoBnd []
                                                                )
                                                                ( NoBnd () )
                                                                ( NoBnd () )
                                                            )
                                                        )
                                                    )
                                                , Same
                                                    ( Fun
                                                        ( bind
                                                            ( w_, x )
                                                            ( DConF "true" []
                                                                ( "Bool"
                                                                , NoBnd []
                                                                )
                                                                ( NoBnd () )
                                                                ( NoBnd () )
                                                            )
                                                        )
                                                    ) dummyInfo
                                                    ( Pi
                                                        ( Same
                                                            ( TConF "Bool" []
                                                                ( NoBnd () )
                                                                ( NoBnd () )
                                                            ) dummyInfo TyU
                                                            ( TConF "Bool" []
                                                                ( NoBnd () )
                                                                ( NoBnd () )
                                                            )
                                                        )
                                                        ( bind w_
                                                            ( Same
                                                                ( TConF "Bool" []
                                                                    ( NoBnd () )
                                                                    ( NoBnd () )
                                                                ) dummyInfo TyU
                                                                ( TConF "Bool" []
                                                                    ( NoBnd () )
                                                                    ( NoBnd () )
                                                                )
                                                            )
                                                        )
                                                    )
                                                    ( Fun
                                                        ( bind
                                                            ( w_, x )
                                                            ( DConF "false" []
                                                                ( "Bool"
                                                                , NoBnd []
                                                                )
                                                                ( NoBnd () )
                                                                ( NoBnd () )
                                                            )
                                                        )
                                                    )
                                                ]
                                                ( NoBnd () )
                                                ( TelBnd TyU
                                                    ( bind aA
                                                        ( TelBnd ( V aA )
                                                            ( bind w_
                                                                ( TelBnd ( V aA )
                                                                    ( bind _1
                                                                        ( NoBnd () )
                                                                    )
                                                                )
                                                            )
                                                        )
                                                    )
                                                )
                                            )
                                        ) TyU
                                        ( Pi
                                            ( TConF "Bool" []
                                                ( NoBnd () )
                                                ( NoBnd () )
                                            )
                                            ( bind _3
                                                ( TConF "Bool" []
                                                    ( NoBnd () )
                                                    ( NoBnd () )
                                                )
                                            )
                                        )
                                    ) TyU
                                    ( Pi
                                        ( TConF "Bool" []
                                            ( NoBnd () )
                                            ( NoBnd () )
                                        )
                                        ( bind _3
                                            ( TConF "Bool" []
                                                ( NoBnd () )
                                                ( NoBnd () )
                                            )
                                        )
                                    )
                                )
                            )
                        )
                        ( DConF "true" []
                            ( "Bool", NoBnd [] )
                            ( NoBnd () )
                            ( NoBnd () )
                        )
                    )
                )



e2 = ( App
    ( DConF "refl" []
        ( "Id"
        , TelBnd TyU
            ( bind aA
                ( TelBnd ( V aA )
                    ( bind a ( NoBnd [ V aA, V a, V a ] ) )
                )
            )
        )
        ( TelBnd TyU
            ( bind aA
                ( TelBnd ( V aA ) ( bind a ( NoBnd () ) ) )
            )
        )
        ( TelBnd TyU
            ( bind aA
                ( TelBnd ( V aA )
                    ( bind _3
                        ( TelBnd ( V aA )
                            ( bind _4 ( NoBnd () ) )
                        )
                    )
                )
            )
        )
    )
    ( TConF "Bool" [] ( NoBnd () ) ( NoBnd () ) )
            )


h :: Name a
( aA, w_, _1, _2, _3, _4, a, h, p_, x ) =
    ( s2n "A"
    , s2n "_"
    , s2n "_1"
    , s2n "_2"
    , s2n "_3"
    , s2n "_4"
    , s2n "a"
    , s2n "h"
    , s2n "p_"
    , s2n "x"
    ) 
exp = Case
    [ Fun
        ( bind
            ( w_, x )
            ( DConF "true" [] ( "Bool", NoBnd [] ) ( NoBnd () ) ( NoBnd () ) )
        )
    , Fun
        ( bind
            ( w_, x )
            ( DConF "false" [] ( "Bool", NoBnd [] ) ( NoBnd () ) ( NoBnd () ) )
        )
    , C
        ( App
            ( App
                ( DConF "refl" []
                    ( "Id"
                    , TelBnd TyU
                        ( bind aA
                            ( TelBnd ( V aA )
                                ( bind a ( NoBnd [ V aA, V a, V a ] ) )
                            )
                        )
                    )
                    ( TelBnd TyU
                        ( bind aA ( TelBnd ( V aA ) ( bind a ( NoBnd () ) ) ) )
                    )
                    ( TelBnd TyU
                        ( bind aA
                            ( TelBnd ( V aA )
                                ( bind w_
                                    ( TelBnd ( V aA ) ( bind _1 ( NoBnd () ) ) )
                                )
                            )
                        )
                    )
                )
                ( Pi
                    ( TConF "Bool" [] ( NoBnd () ) ( NoBnd () ) )
                    ( bind w_ ( TConF "Bool" [] ( NoBnd () ) ( NoBnd () ) ) )
                )
            )
            ( Fun
                ( bind
                    ( w_, x )
                    ( DConF "true" []
                        ( "Bool", NoBnd [] )
                        ( NoBnd () )
                        ( NoBnd () )
                    )
                )
            )
        )
        ( Same
            ( TConF "Id"
                [ Pi
                    ( TConF "Bool" [] ( NoBnd () ) ( NoBnd () ) )
                    ( bind w_ ( TConF "Bool" [] ( NoBnd () ) ( NoBnd () ) ) )
                , Fun
                    ( bind
                        ( w_, x )
                        ( DConF "true" []
                            ( "Bool", NoBnd [] )
                            ( NoBnd () )
                            ( NoBnd () )
                        )
                    )
                , Fun
                    ( bind
                        ( w_, x )
                        ( DConF "true" []
                            ( "Bool", NoBnd [] )
                            ( NoBnd () )
                            ( NoBnd () )
                        )
                    )
                ]
                ( NoBnd () )
                ( TelBnd TyU
                    ( bind aA
                        ( TelBnd ( V aA )
                            ( bind w_
                                ( TelBnd ( V aA ) ( bind _1 ( NoBnd () ) ) )
                            )
                        )
                    )
                )
            ) dummyInfo  TyU
            ( App
                ( App
                    ( App
                        ( TConF "Id" []
                            ( TelBnd TyU
                                ( bind aA
                                    ( TelBnd ( V aA )
                                        ( bind w_
                                            ( TelBnd ( V aA )
                                                ( bind _1 ( NoBnd () ) )
                                            )
                                        )
                                    )
                                )
                            )
                            ( TelBnd TyU
                                ( bind aA
                                    ( TelBnd ( V aA )
                                        ( bind w_
                                            ( TelBnd ( V aA )
                                                ( bind _1 ( NoBnd () ) )
                                            )
                                        )
                                    )
                                )
                            )
                        )
                        ( Pi
                            ( TConF "Bool" [] ( NoBnd () ) ( NoBnd () ) )
                            ( bind w_
                                ( TConF "Bool" [] ( NoBnd () ) ( NoBnd () ) )
                            )
                        )
                    )
                    ( Fun
                        ( bind
                            ( w_, x )
                            ( DConF "true" []
                                ( "Bool", NoBnd [] )
                                ( NoBnd () )
                                ( NoBnd () )
                            )
                        )
                    )
                )
                ( Fun
                    ( bind
                        ( w_, x )
                        ( DConF "false" []
                            ( "Bool", NoBnd [] )
                            ( NoBnd () )
                            ( NoBnd () )
                        )
                    )
                )
            )
        )
    ]
    [ Match
        ( bind
            [ PVar _2, PVar _1, Pat "refl" [ PVar w_, PVar h ] p_ ]
            ( C
                ( C
                    ( C
                        ( App
                            ( App
                                ( DConF "refl" []
                                    ( "Id"
                                    , TelBnd TyU
                                        ( bind aA
                                            ( TelBnd ( V aA )
                                                ( bind a
                                                    ( NoBnd [ V aA, V a, V a ] )
                                                )
                                            )
                                        )
                                    )
                                    ( TelBnd TyU
                                        ( bind aA
                                            ( TelBnd ( V aA )
                                                ( bind a ( NoBnd () ) )
                                            )
                                        )
                                    )
                                    ( TelBnd TyU
                                        ( bind aA
                                            ( TelBnd ( V aA )
                                                ( bind _3
                                                    ( TelBnd ( V aA )
                                                        ( bind _4( NoBnd () ) )
                                                    )
                                                )
                                            )
                                        )
                                    )
                                )
                                ( TConF "Bool" [] ( NoBnd () ) ( NoBnd () ) )
                            )
                            ( App
                                ( C ( V h )
                                    ( Union ( V w_ ) TyU
                                        ( Union
                                            ( Union
                                                ( Tind 0 ( V p_ ) ) TyU
                                                ( Pi
                                                    ( TConF "Bool" []
                                                        ( NoBnd () )
                                                        ( NoBnd () )
                                                    )
                                                    ( bind _3
                                                        ( TConF "Bool" []
                                                            ( NoBnd () )
                                                            ( NoBnd () )
                                                        )
                                                    )
                                                )
                                            ) TyU
                                            ( Pi
                                                ( TConF "Bool" []
                                                    ( NoBnd () )
                                                    ( NoBnd () )
                                                )
                                                ( bind _3
                                                    ( TConF "Bool" []
                                                        ( NoBnd () )
                                                        ( NoBnd () )
                                                    )
                                                )
                                            )
                                        )
                                    )
                                )
                                ( DConF "true" []
                                    ( "Bool", NoBnd [] )
                                    ( NoBnd () )
                                    ( NoBnd () )
                                )
                            )
                        )
                        ( TConF "Id"
                            [ TConF "Bool" []
                                ( NoBnd () )
                                ( NoBnd () )
                            , App
                                ( C
                                    ( Union ( V h )
                                        ( Tind 0 ( V p_ ) )
                                        ( Union
                                            ( Union ( V h )
                                                ( Union
                                                    ( Tind 0 ( V p_ ) ) TyU
                                                    ( Tind 0 ( V p_ ) )
                                                )
                                                ( Union
                                                    ( Tind 1 ( V p_ ) )
                                                    ( Union
                                                        ( Tind 0 ( V p_ ) ) TyU
                                                        ( Tind 0 ( V p_ ) )
                                                    ) ( V _2 )
                                                )
                                            )
                                            ( Tind 0 ( V p_ ) ) ( V _2 )
                                        )
                                    )
                                    ( Union
                                        ( Union ( V w_ ) TyU
                                            ( Union
                                                ( Union
                                                    ( Tind 0 ( V p_ ) ) TyU
                                                    ( Pi
                                                        ( TConF "Bool" []
                                                            ( NoBnd () )
                                                            ( NoBnd () )
                                                        )
                                                        ( bind _3
                                                            ( TConF "Bool" []
                                                                ( NoBnd () )
                                                                ( NoBnd () )
                                                            )
                                                        )
                                                    )
                                                ) TyU
                                                ( Pi
                                                    ( TConF "Bool" []
                                                        ( NoBnd () )
                                                        ( NoBnd () )
                                                    )
                                                    ( bind _3
                                                        ( TConF "Bool" []
                                                            ( NoBnd () )
                                                            ( NoBnd () )
                                                        )
                                                    )
                                                )
                                            )
                                        ) TyU
                                        ( Union
                                            ( Union
                                                ( Tind 0 ( V p_ ) ) TyU
                                                ( Pi
                                                    ( TConF "Bool" []
                                                        ( NoBnd () )
                                                        ( NoBnd () )
                                                    )
                                                    ( bind _3
                                                        ( TConF "Bool" []
                                                            ( NoBnd () )
                                                            ( NoBnd () )
                                                        )
                                                    )
                                                )
                                            ) TyU
                                            ( Pi
                                                ( TConF "Bool" []
                                                    ( NoBnd () )
                                                    ( NoBnd () )
                                                )
                                                ( bind _3
                                                    ( TConF "Bool" []
                                                        ( NoBnd () )
                                                        ( NoBnd () )
                                                    )
                                                )
                                            )
                                        )
                                    )
                                )
                                ( DConF "true" []
                                    ( "Bool", NoBnd [] )
                                    ( NoBnd () )
                                    ( NoBnd () )
                                )
                            , App
                                ( C
                                    ( Union ( V h )
                                        ( Tind 0 ( V p_ ) )
                                        ( Union
                                            ( Union ( V h )
                                                ( Union
                                                    ( Tind 0 ( V p_ ) ) TyU
                                                    ( Tind 0 ( V p_ ) )
                                                )
                                                ( Union
                                                    ( Tind 1 ( V p_ ) )
                                                    ( Union
                                                        ( Tind 0 ( V p_ ) ) TyU
                                                        ( Tind 0 ( V p_ ) )
                                                    ) ( V _2 )
                                                )
                                            )
                                            ( Tind 0 ( V p_ ) ) ( V _2 )
                                        )
                                    )
                                    ( Union
                                        ( Union ( V w_ ) TyU
                                            ( Union
                                                ( Union
                                                    ( Tind 0 ( V p_ ) ) TyU
                                                    ( Pi
                                                        ( TConF "Bool" []
                                                            ( NoBnd () )
                                                            ( NoBnd () )
                                                        )
                                                        ( bind _3
                                                            ( TConF "Bool" []
                                                                ( NoBnd () )
                                                                ( NoBnd () )
                                                            )
                                                        )
                                                    )
                                                ) TyU
                                                ( Pi
                                                    ( TConF "Bool" []
                                                        ( NoBnd () )
                                                        ( NoBnd () )
                                                    )
                                                    ( bind _3
                                                        ( TConF "Bool" []
                                                            ( NoBnd () )
                                                            ( NoBnd () )
                                                        )
                                                    )
                                                )
                                            )
                                        ) TyU
                                        ( Union
                                            ( Union
                                                ( Tind 0 ( V p_ ) ) TyU
                                                ( Pi
                                                    ( TConF "Bool" []
                                                        ( NoBnd () )
                                                        ( NoBnd () )
                                                    )
                                                    ( bind _3
                                                        ( TConF "Bool" []
                                                            ( NoBnd () )
                                                            ( NoBnd () )
                                                        )
                                                    )
                                                )
                                            ) TyU
                                            ( Pi
                                                ( TConF "Bool" []
                                                    ( NoBnd () )
                                                    ( NoBnd () )
                                                )
                                                ( bind _3
                                                    ( TConF "Bool" []
                                                        ( NoBnd () )
                                                        ( NoBnd () )
                                                    )
                                                )
                                            )
                                        )
                                    )
                                )
                                ( DConF "true" []
                                    ( "Bool", NoBnd [] )
                                    ( NoBnd () )
                                    ( NoBnd () )
                                )
                            ]
                            ( NoBnd () )
                            ( TelBnd TyU
                                ( bind aA
                                    ( TelBnd ( V aA )
                                        ( bind _3
                                            ( TelBnd ( V aA )
                                                ( bind _4( NoBnd () ) )
                                            )
                                        )
                                    )
                                )
                            )
                        )
                    )
                    ( Same
                        ( TConF "Id"
                            [ TConF "Bool" []
                                ( NoBnd () )
                                ( NoBnd () )
                            , App
                                ( C ( V _2 )
                                    ( Union
                                        ( Pi
                                            ( TConF "Bool" []
                                                ( NoBnd () )
                                                ( NoBnd () )
                                            )
                                            ( bind _3
                                                ( TConF "Bool" []
                                                    ( NoBnd () )
                                                    ( NoBnd () )
                                                )
                                            )
                                        ) TyU
                                        ( Union
                                            ( Union
                                                ( Tind 0 ( V p_ ) ) TyU
                                                ( Pi
                                                    ( TConF "Bool" []
                                                        ( NoBnd () )
                                                        ( NoBnd () )
                                                    )
                                                    ( bind _3
                                                        ( TConF "Bool" []
                                                            ( NoBnd () )
                                                            ( NoBnd () )
                                                        )
                                                    )
                                                )
                                            ) TyU
                                            ( Pi
                                                ( TConF "Bool" []
                                                    ( NoBnd () )
                                                    ( NoBnd () )
                                                )
                                                ( bind _3
                                                    ( TConF "Bool" []
                                                        ( NoBnd () )
                                                        ( NoBnd () )
                                                    )
                                                )
                                            )
                                        )
                                    )
                                )
                                ( DConF "true" []
                                    ( "Bool", NoBnd [] )
                                    ( NoBnd () )
                                    ( NoBnd () )
                                )
                            , App
                                ( C ( V _2 )
                                    ( Union
                                        ( Pi
                                            ( TConF "Bool" []
                                                ( NoBnd () )
                                                ( NoBnd () )
                                            )
                                            ( bind _3
                                                ( TConF "Bool" []
                                                    ( NoBnd () )
                                                    ( NoBnd () )
                                                )
                                            )
                                        ) TyU
                                        ( Union
                                            ( Union
                                                ( Tind 0 ( V p_ ) ) TyU
                                                ( Pi
                                                    ( TConF "Bool" []
                                                        ( NoBnd () )
                                                        ( NoBnd () )
                                                    )
                                                    ( bind _3
                                                        ( TConF "Bool" []
                                                            ( NoBnd () )
                                                            ( NoBnd () )
                                                        )
                                                    )
                                                )
                                            ) TyU
                                            ( Pi
                                                ( TConF "Bool" []
                                                    ( NoBnd () )
                                                    ( NoBnd () )
                                                )
                                                ( bind _3
                                                    ( TConF "Bool" []
                                                        ( NoBnd () )
                                                        ( NoBnd () )
                                                    )
                                                )
                                            )
                                        )
                                    )
                                )
                                ( DConF "true" []
                                    ( "Bool", NoBnd [] )
                                    ( NoBnd () )
                                    ( NoBnd () )
                                )
                            ]
                            ( NoBnd () )
                            ( TelBnd TyU
                                ( bind aA
                                    ( TelBnd ( V aA )
                                        ( bind _3
                                            ( TelBnd ( V aA )
                                                ( bind _4( NoBnd () ) )
                                            )
                                        )
                                    )
                                )
                            )
                        ) dummyInfo TyU
                        ( App
                            ( App
                                ( App
                                    ( TConF "Id" []
                                        ( TelBnd TyU
                                            ( bind aA
                                                ( TelBnd ( V aA )
                                                    ( bind _3
                                                        ( TelBnd ( V aA )
                                                            ( bind _4
                                                                ( NoBnd () )
                                                            )
                                                        )
                                                    )
                                                )
                                            )
                                        )
                                        ( TelBnd TyU
                                            ( bind aA
                                                ( TelBnd ( V aA )
                                                    ( bind _3
                                                        ( TelBnd ( V aA )
                                                            ( bind _4
                                                                ( NoBnd () )
                                                            )
                                                        )
                                                    )
                                                )
                                            )
                                        )
                                    )
                                    ( TConF "Bool" []
                                        ( NoBnd () )
                                        ( NoBnd () )
                                    )
                                )
                                ( App ( V _2 )
                                    ( DConF "true" []
                                        ( "Bool", NoBnd [] )
                                        ( NoBnd () )
                                        ( NoBnd () )
                                    )
                                )
                            )
                            ( App
                                ( C ( V _2 ) ( Tind 0 ( V p_ ) ) )
                                ( DConF "true" []
                                    ( "Bool", NoBnd [] )
                                    ( NoBnd () )
                                    ( NoBnd () )
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
                                    ( bind aA
                                        ( TelBnd ( V aA )
                                            ( bind _3
                                                ( TelBnd ( V aA )
                                                    ( bind _4( NoBnd () ) )
                                                )
                                            )
                                        )
                                    )
                                )
                                ( TelBnd TyU
                                    ( bind aA
                                        ( TelBnd ( V aA )
                                            ( bind _3
                                                ( TelBnd ( V aA )
                                                    ( bind _4( NoBnd () ) )
                                                )
                                            )
                                        )
                                    )
                                )
                            )
                            ( TConF "Bool" [] ( NoBnd () ) ( NoBnd () ) )
                        )
                        ( App ( V _2 )
                            ( DConF "true" []
                                ( "Bool", NoBnd [] )
                                ( NoBnd () )
                                ( NoBnd () )
                            )
                        )
                    )
                    ( App
                        ( Union ( V _1 )
                            ( Tind 0 ( V p_ ) )
                            ( Union
                                ( Union ( V h )
                                    ( Union
                                        ( Tind 0 ( V p_ ) ) TyU
                                        ( Tind 0 ( V p_ ) )
                                    )
                                    ( Union
                                        ( Tind 1 ( V p_ ) )
                                        ( Union
                                            ( Tind 0 ( V p_ ) ) TyU
                                            ( Tind 0 ( V p_ ) )
                                        ) ( V _2 )
                                    )
                                )
                                ( Union
                                    ( Tind 0 ( V p_ ) ) TyU
                                    ( Tind 0 ( V p_ ) )
                                )
                                ( Union
                                    ( Union ( V h )
                                        ( Union
                                            ( Tind 0 ( V p_ ) ) TyU
                                            ( Tind 0 ( V p_ ) )
                                        )
                                        ( Union
                                            ( Tind 2 ( V p_ ) )
                                            ( Union
                                                ( Tind 0 ( V p_ ) ) TyU
                                                ( Tind 0 ( V p_ ) )
                                            ) ( V _1 )
                                        )
                                    )
                                    ( Union
                                        ( Tind 0 ( V p_ ) ) TyU
                                        ( Tind 0 ( V p_ ) )
                                    ) ( V _1 )
                                )
                            )
                        )
                        ( DConF "true" []
                            ( "Bool", NoBnd [] )
                            ( NoBnd () )
                            ( NoBnd () )
                        )
                    )
                )
            )
        )
    ]
    ( An ( Just ( [], Nothing) ) )
