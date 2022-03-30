module Dynamic.Ex6 where


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

e0  = isValue ee

( _36, m23, p_35, _, p, p_ ) = ( s2n "_36", s2n "m23", s2n "p_35", s2n "_", s2n "p", s2n "p_" ) 
eee1= Case
        [ C
            ( DConF "S" [ V _36 ]
                ( "Nat", NoBnd [] )
                ( TelBnd
                    ( TConF "Nat" [] ( NoBnd () ) ( NoBnd () ) )
                    ( u ( NoBnd () ) )
                )
                ( NoBnd () )
            ) ( V p_35 )
        ]
        [ 
          Match ( bind [ Pat "Z" [] p_ ] ( V m23 ) )
         , 
        Match
            ( bind
                [ Pat "S" [ PVar p ] p_ ]
                ( App
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
                    ( App ( App ( Ref "add" ) ( V p ) ) ( V m23 ) )
                )
            )
        ] ( An Nothing )


ee1 = runFreshM $ whnf eee1


p_29 = s2n "p_29"
eee = Case
        [ C
            ( DConF "Z" []
                ( "Nat", NoBnd [] )
                ( NoBnd () )
                ( NoBnd () )
            ) ( V p_29 ) -- this blocks normalization
        ]
        [ Match
            ( bind [ Pat "Z" [] p_ ] ( V m23 ) )
        -- , Match
        --     ( bind
        --         [ Pat "S" [ PVar p ] p_ ]
        --         ( App
        --             ( DConF "S" []
        --                 ( "Nat"
        --                 , TelBnd
        --                     ( TConF "Nat" [] ( NoBnd () ) ( NoBnd () ) )
        --                     ( u ( NoBnd [] ) )
        --                 )
        --                 ( TelBnd
        --                     ( TConF "Nat" [] ( NoBnd () ) ( NoBnd () ) )
        --                     ( u ( NoBnd () ) )
        --                 )
        --                 ( NoBnd () )
        --             )
        --             ( App ( App ( Ref "add" ) ( V p ) ) ( V m23 ) )
        --         )
        --     )
        ] ( An Nothing )

ee0 = runFreshM $ whnf eee


sss =let _=s2n "_" in Union
    ( DConF "Z" [] ( "Nat", NoBnd [] ) ( NoBnd () ) ( NoBnd () ) )
    ( TConF "Nat" [] ( NoBnd () ) ( NoBnd () ) )
    ( Dind 0
        ( Union
            ( DConF "S"
                [ DConF "Z" [] ( "Nat", NoBnd [] ) ( NoBnd () ) ( NoBnd () ) ]
                ( "Nat", NoBnd [] )
                ( TelBnd
                    ( TConF "Nat" [] ( NoBnd () ) ( NoBnd () ) )
                    ( u ( NoBnd () ) )
                )
                ( NoBnd () )
            )
            ( TConF "Nat" [] ( NoBnd () ) ( NoBnd () ) )
            ( DConF "Nat"
                [ C
                    ( DConF "Nat" []
                        ( "Nat", NoBnd [] )
                        ( NoBnd () )
                        ( NoBnd () )
                    )
                    ( TConF "Nat" [] ( NoBnd () ) ( NoBnd () ) )
                ]
                ( "Nat", NoBnd [] )
                ( TelBnd
                    ( TConF "Nat" [] ( NoBnd () ) ( NoBnd () ) )
                    ( u( NoBnd () ) )
                )
                ( NoBnd () )
            )
        )
    )



(a, _, _1, _2, n ) = ( s2n "a", s2n "_", s2n "_1", s2n "_2", s2n "n" ) 

trm = ( DConF "Cons"
        [ TConF "Bool" []
            ( NoBnd () )
            ( NoBnd () )
        , DConF "true" []
            ( "Bool", NoBnd [] )
            ( NoBnd () )
            ( NoBnd () )
        , DConF "Z" []
            ( "Nat", NoBnd [] )
            ( NoBnd () )
            ( NoBnd () )
        , C
            ( DConF "Nil"
                [ TConF "Bool" [] ( NoBnd () ) ( NoBnd () ) ]
                ( "Vec"
                , NoBnd
                    [ TConF "Bool" []
                        ( NoBnd () )
                        ( NoBnd () )
                    , DConF "Z" []
                        ( "Nat", NoBnd [] )
                        ( NoBnd () )
                        ( NoBnd () )
                    ]
                )
                ( TelBnd TyU ( u ( NoBnd () ) ) )
                ( TelBnd TyU
                    ( u
                        ( TelBnd
                            ( TConF "Nat" [] ( NoBnd () ) ( NoBnd () ) )
                            ( u ( NoBnd () ) )
                        )
                    )
                )
            )
            ( TConF "Vec"
                [ TConF "Bool" []
                    ( NoBnd () )
                    ( NoBnd () )
                , C
                    ( DConF "Z" []
                        ( "Nat", NoBnd [] )
                        ( NoBnd () )
                        ( NoBnd () )
                    )
                    ( TConF "Nat" [] ( NoBnd () ) ( NoBnd () ) )
                ]
                ( NoBnd () )
                ( TelBnd TyU
                    ( u
                        ( TelBnd
                            ( TConF "Nat" [] ( NoBnd () ) ( NoBnd () ) )
                            ( u ( NoBnd () ) )
                        )
                    )
                )
            )
        ]
        ( "Vec"
        , NoBnd
            [ TConF "Bool" []
                ( NoBnd () )
                ( NoBnd () )
            , App
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
                ( DConF "Z" [] ( "Nat", NoBnd [] ) ( NoBnd () ) ( NoBnd () ) )
            ]
        )
        ( TelBnd TyU
            ( bind a
                ( TelBnd ( V a )
                    ( u
                        ( TelBnd
                            ( TConF "Nat" [] ( NoBnd () ) ( NoBnd () ) )
                            ( bind n
                                ( TelBnd
                                    ( App
                                        ( App
                                            ( TConF "Vec" []
                                                ( TelBnd TyU
                                                    ( u
                                                        ( TelBnd
                                                            ( TConF "Nat" []
                                                                ( NoBnd () )
                                                                ( NoBnd () )
                                                            )
                                                            ( u
                                                                ( NoBnd () )
                                                            )
                                                        )
                                                    )
                                                )
                                                ( TelBnd TyU
                                                    ( u
                                                        ( TelBnd
                                                            ( TConF "Nat" []
                                                                ( NoBnd () )
                                                                ( NoBnd () )
                                                            )
                                                            ( u
                                                                ( NoBnd () )
                                                            )
                                                        )
                                                    )
                                                )
                                            ) ( V a )
                                        ) ( V n )
                                    )
                                    ( u ( NoBnd () ) )
                                )
                            )
                        )
                    )
                )
            )
        )
        ( TelBnd TyU
            ( u
                ( TelBnd
                    ( TConF "Nat" [] ( NoBnd () ) ( NoBnd () ) )
                    ( u ( NoBnd () ) )
                )
            )
        )
    )

ls = [ Union ( TConF "Bool" [] ( NoBnd () ) ( NoBnd () ) ) TyU ( TConF "Bool" [] ( NoBnd () ) ( NoBnd () ) )
        , Union
            ( DConF "S"
                [ C
                    ( DConF "Z" []
                        ( "Nat", NoBnd [] )
                        ( NoBnd () )
                        ( NoBnd () )
                    )
                    ( TConF "Nat" [] ( NoBnd () ) ( NoBnd () ) )
                ]
                ( "Nat", NoBnd [] )
                ( TelBnd
                    ( TConF "Nat" [] ( NoBnd () ) ( NoBnd () ) )
                    ( u ( NoBnd () ) )
                )
                ( NoBnd () )
            )
            ( TConF "Nat" [] ( NoBnd () ) ( NoBnd () ) )
            ( DConF "S"
                [ C
                    ( DConF "Z" []
                        ( "Nat", NoBnd [] )
                        ( NoBnd () )
                        ( NoBnd () )
                    )
                    ( TConF "Nat" [] ( NoBnd () ) ( NoBnd () ) )
                ]
                ( "Nat", NoBnd [] )
                ( TelBnd
                    ( TConF "Nat" [] ( NoBnd () ) ( NoBnd () ) )
                    ( u ( NoBnd () ) )
                )
                ( NoBnd () )
            )
        ]
ev = ( TConF "Vec"
   ls
        ( NoBnd () )
        ( TelBnd TyU
            ( u
                ( TelBnd
                    ( TConF "Nat" [] ( NoBnd () ) ( NoBnd () ) )
                    ( u ( NoBnd () ) )
                )
            )
        )
    )
ee =  C trm ev
    
    
