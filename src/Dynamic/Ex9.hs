module Dynamic.Ex9 where


import Dynamic.Ast 
import Dynamic.Norm ( isValue, whnf, cbvErrNext, cbvOrErr, whnfd ) 
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
import Prelude hiding (head, exp)
import Data.Functor.Identity
import Control.Monad.Except



rr e = runIdentity $ runExceptT $ runFreshMT $ runWithModuleMT ( e) stdModule
e0 = runFreshM $ Dynamic.Norm.whnf exp





exp = App
    -- ( Ref "head" )
    head
    ( C
        ( DConF "Nil" []
            ( "Vec"
            , NoBnd
                [ DConF "Z" [] ( "Nat", NoBnd [] ) ( NoBnd () ) ( NoBnd () ) ]
            )
            ( NoBnd () )
            ( TelBnd
                ( TConF "Nat" [] ( NoBnd () ) ( NoBnd () ) )
                ( u ( NoBnd () ) )
            )
        )
        ( Same
            ( TConF "Vec"
                [ DConF "Z" [] ( "Nat", NoBnd [] ) ( NoBnd () ) ( NoBnd () ) ]
                ( NoBnd () )
                ( TelBnd
                    ( TConF "Nat" [] ( NoBnd () ) ( NoBnd () ) )
                    ( u ( NoBnd () ) )
                )
            ) dummyInfo TyU
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
                    ( DConF "Z" []
                        ( "Nat", NoBnd [] )
                        ( NoBnd () )
                        ( NoBnd () )
                    )
                )
            )
        )
    )

( wild, a, p_, v ) =
    ( s2n "_", s2n "a", s2n "p_", s2n "v" ) 
head =  Fun
    ( bind
        ( wild, v )
        ( Case [ V v ]
            [ Match
                ( bind [ Pat "Cons" [ PVar a ] p_ ] ( V a ) )
            , Match
                ( bind
                    [ Pat "Nil" [] p_ ]
                    ( C
                        ( Tind 0 ( V p_ ) )
                        ( TConF "Nat" [] ( NoBnd () ) ( NoBnd () ) )
                    )
                )
            ]
            ( An ( Just ( [], Nothing) ) )
        )
    )








-- ( __, a, p_ ) = ( s2n "_", s2n "a", s2n "p_" )  
-- exp = Case
--     [ C
--         ( DConF "Nil" []
--             ( "Vec"
--             , NoBnd
--                 [ DConF "Z" [] ( "Nat", NoBnd [] ) ( NoBnd () ) ( NoBnd () ) ]
--             )
--             ( NoBnd () )
--             ( TelBnd
--                 ( TConF "Nat" [] ( NoBnd () ) ( NoBnd () ) )
--                 ( bind __ ( NoBnd () ) )
--             )
--         )
--         ( Same
--             ( TConF "Vec"
--                 [ DConF "Z" [] ( "Nat", NoBnd [] ) ( NoBnd () ) ( NoBnd () ) ]
--                 ( NoBnd () )
--                 ( TelBnd
--                     ( TConF "Nat" [] ( NoBnd () ) ( NoBnd () ) )
--                     ( bind __ ( NoBnd () ) )
--                 )
--             ) dummyInfo TyU
--             ( App
--                 ( TConF "Vec" []
--                     ( TelBnd
--                         ( TConF "Nat" [] ( NoBnd () ) ( NoBnd () ) )
--                         ( bind __ ( NoBnd () ) )
--                     )
--                     ( TelBnd
--                         ( TConF "Nat" [] ( NoBnd () ) ( NoBnd () ) )
--                         ( bind __ ( NoBnd () ) )
--                     )
--                 )
--                 ( App
--                     ( DConF "S" []
--                         ( "Nat"
--                         , TelBnd
--                             ( TConF "Nat" [] ( NoBnd () ) ( NoBnd () ) )
--                             ( bind __ ( NoBnd [] ) )
--                         )
--                         ( TelBnd
--                             ( TConF "Nat" [] ( NoBnd () ) ( NoBnd () ) )
--                             ( bind __ ( NoBnd () ) )
--                         )
--                         ( NoBnd () )
--                     )
--                     ( DConF "Z" []
--                         ( "Nat", NoBnd [] )
--                         ( NoBnd () )
--                         ( NoBnd () )
--                     )
--                 )
--             )
--         )
--     ]
--     [ Match
--         ( bind [ Pat "Cons" [ PVar a ] p_ ] ( V a ) )
--     , Match
--         ( bind
--             [ Pat "Nil" [] p_ ]
--             ( Blame
--                 ( Tind 0 ( V p_ ) )
--                 ( TConF "Nat" [] ( NoBnd () ) ( NoBnd () ) )
--             )
--         )
--     ]
--     ( An ( Just ( [], Nothing ) ) )
