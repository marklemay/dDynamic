
ee = ( let
        ( _
        , _1
        , _2
        , _3
        , _4
        , _5
        , a
        , aTy
        , aTy1
        , ab
        , p_
        , x
        , x1
        , xb
        , xt
        , xy
        , y
        , yb
        , yt
        ) =
        ( s2n "_"
        , s2n "_1"
        , s2n "_2"
        , s2n "_3"
        , s2n "_4"
        , s2n "_5"
        , s2n "a"
        , s2n "aTy"
        , s2n "aTy1"
        , s2n "ab"
        , s2n "p_"
        , s2n "x"
        , s2n "x1"
        , s2n "xb"
        , s2n "xt"
        , s2n "xy"
        , s2n "y"
        , s2n "yb"
        , s2n "yt"
        ) in Module fromList
        [
            ( "Id"
            , DataDef
                ( TelBnd TyU
                    ( bind a
                        ( TelBnd ( V a )
                            ( bind _
                                ( TelBnd ( V a ) ( bind _1 ( NoBnd () ) ) )
                            )
                        )
                    )
                ) fromList
                [
                    ( "Refl"
                    , TelBnd TyU
                        ( bind a
                            ( TelBnd ( V a )
                                ( bind x ( NoBnd [ V a, V x, V x ] ) )
                            )
                        )
                    )
                ]
            )
        ]
        ( DefCtx fromList
            [
                ( "sym"
                ,
                    ( Fun
                        ( bind
                            ( _, aTy )
                            ( Fun
                                ( bind
                                    ( _1, x )
                                    ( Fun
                                        ( bind
                                            ( _2, y )
                                            ( Fun
                                                ( bind
                                                    ( _3, xy )
                                                    ( C
                                                        ( Case
                                                            [ V x
                                                            , V y
                                                            , C ( V xy )
                                                                ( Same
                                                                    ( App
                                                                        ( App
                                                                            ( App
                                                                                ( TConF "Id" []
                                                                                    ( TelBnd TyU
                                                                                        ( bind a
                                                                                            ( TelBnd ( V a )
                                                                                                ( bind _4
                                                                                                    ( TelBnd ( V a )
                                                                                                        ( bind _5
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
                                                                                                ( bind _4
                                                                                                    ( TelBnd ( V a )
                                                                                                        ( bind _5
                                                                                                            ( NoBnd () )
                                                                                                        )
                                                                                                    )
                                                                                                )
                                                                                            )
                                                                                        )
                                                                                    )
                                                                                ) ( V aTy )
                                                                            ) ( V x )
                                                                        ) ( V y )
                                                                    )
                                                                    ( Info Nothing [] ) TyU
                                                                    ( App
                                                                        ( App
                                                                            ( App
                                                                                ( TConF "Id" []
                                                                                    ( TelBnd TyU
                                                                                        ( bind a
                                                                                            ( TelBnd ( V a )
                                                                                                ( bind _4
                                                                                                    ( TelBnd ( V a )
                                                                                                        ( bind _5
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
                                                                                                ( bind _4
                                                                                                    ( TelBnd ( V a )
                                                                                                        ( bind _5
                                                                                                            ( NoBnd () )
                                                                                                        )
                                                                                                    )
                                                                                                )
                                                                                            )
                                                                                        )
                                                                                    )
                                                                                ) ( V aTy )
                                                                            ) ( V aTy )
                                                                        ) ( V aTy )
                                                                    )
                                                                )
                                                            ]
                                                            [ Match
                                                                ( bind
                                                                    [ PVar xb
                                                                    , PVar yb
                                                                    , Pat "Refl"
                                                                        [ PVar aTy1
                                                                        , PVar ab
                                                                        ] p_
                                                                    ]
                                                                    ( C
                                                                        ( C
                                                                            ( App
                                                                                ( C
                                                                                    ( App
                                                                                        ( DConF "Refl" []
                                                                                            ( "Id"
                                                                                            , TelBnd TyU
                                                                                                ( bind a
                                                                                                    ( TelBnd ( V a )
                                                                                                        ( bind x1
                                                                                                            ( NoBnd
                                                                                                                [ V a
                                                                                                                , V x1
                                                                                                                , V x1
                                                                                                                ]
                                                                                                            )
                                                                                                        )
                                                                                                    )
                                                                                                )
                                                                                            )
                                                                                            ( TelBnd TyU
                                                                                                ( bind a
                                                                                                    ( TelBnd ( V a )
                                                                                                        ( bind x1
                                                                                                            ( NoBnd () )
                                                                                                        )
                                                                                                    )
                                                                                                )
                                                                                            )
                                                                                            ( TelBnd TyU
                                                                                                ( bind a
                                                                                                    ( TelBnd ( V a )
                                                                                                        ( bind _4
                                                                                                            ( TelBnd ( V a )
                                                                                                                ( bind _5
                                                                                                                    ( NoBnd () )
                                                                                                                )
                                                                                                            )
                                                                                                        )
                                                                                                    )
                                                                                                )
                                                                                            )
                                                                                        ) ( V aTy1 )
                                                                                    )
                                                                                    ( Pi
                                                                                        ( Union ( V aTy1 ) TyU
                                                                                            ( Union
                                                                                                ( Union
                                                                                                    ( Tcon 0 ( V p_ ) ) TyU ( V aTy )
                                                                                                ) TyU ( V aTy )
                                                                                            )
                                                                                        )
                                                                                        ( bind x1
                                                                                            ( TConF "Id"
                                                                                                [ Union ( V aTy1 ) TyU
                                                                                                    ( Union
                                                                                                        ( Union
                                                                                                            ( Tcon 0 ( V p_ ) ) TyU ( V aTy )
                                                                                                        ) TyU ( V aTy )
                                                                                                    )
                                                                                                , V x1
                                                                                                , V x1
                                                                                                ]
                                                                                                ( NoBnd () )
                                                                                                ( TelBnd TyU
                                                                                                    ( bind a
                                                                                                        ( TelBnd ( V a )
                                                                                                            ( bind _4
                                                                                                                ( TelBnd ( V a )
                                                                                                                    ( bind _5
                                                                                                                        ( NoBnd () )
                                                                                                                    )
                                                                                                                )
                                                                                                            )
                                                                                                        )
                                                                                                    )
                                                                                                )
                                                                                            )
                                                                                        )
                                                                                    )
                                                                                )
                                                                                ( C ( V ab )
                                                                                    ( Union ( V aTy1 ) TyU
                                                                                        ( Union
                                                                                            ( Union
                                                                                                ( Tcon 0 ( V p_ ) ) TyU ( V aTy )
                                                                                            ) TyU ( V aTy )
                                                                                        )
                                                                                    )
                                                                                )
                                                                            )
                                                                            ( TConF "Id"
                                                                                [ V aTy
                                                                                , C
                                                                                    ( Union ( V ab )
                                                                                        ( Tcon 0 ( V p_ ) )
                                                                                        ( Union
                                                                                            ( Union ( V ab )
                                                                                                ( Union
                                                                                                    ( Tcon 0 ( V p_ ) ) TyU
                                                                                                    ( Tcon 0 ( V p_ ) )
                                                                                                )
                                                                                                ( Union
                                                                                                    ( Tcon 1 ( V p_ ) )
                                                                                                    ( Union
                                                                                                        ( Tcon 0 ( V p_ ) ) TyU
                                                                                                        ( Tcon 0 ( V p_ ) )
                                                                                                    ) ( V xb )
                                                                                                )
                                                                                            )
                                                                                            ( Tcon 0 ( V p_ ) ) ( V xb )
                                                                                        )
                                                                                    )
                                                                                    ( Union
                                                                                        ( Union ( V aTy1 ) TyU
                                                                                            ( Union
                                                                                                ( Union
                                                                                                    ( Tcon 0 ( V p_ ) ) TyU ( V aTy )
                                                                                                ) TyU ( V aTy )
                                                                                            )
                                                                                        ) TyU
                                                                                        ( Union
                                                                                            ( Union
                                                                                                ( Tcon 0 ( V p_ ) ) TyU ( V aTy )
                                                                                            ) TyU ( V aTy )
                                                                                        )
                                                                                    )
                                                                                , C
                                                                                    ( Union ( V ab )
                                                                                        ( Tcon 0 ( V p_ ) )
                                                                                        ( Union
                                                                                            ( Union ( V ab )
                                                                                                ( Union
                                                                                                    ( Tcon 0 ( V p_ ) ) TyU
                                                                                                    ( Tcon 0 ( V p_ ) )
                                                                                                )
                                                                                                ( Union
                                                                                                    ( Tcon 1 ( V p_ ) )
                                                                                                    ( Union
                                                                                                        ( Tcon 0 ( V p_ ) ) TyU
                                                                                                        ( Tcon 0 ( V p_ ) )
                                                                                                    ) ( V xb )
                                                                                                )
                                                                                            )
                                                                                            ( Tcon 0 ( V p_ ) ) ( V xb )
                                                                                        )
                                                                                    )
                                                                                    ( Union
                                                                                        ( Union ( V aTy1 ) TyU
                                                                                            ( Union
                                                                                                ( Union
                                                                                                    ( Tcon 0 ( V p_ ) ) TyU ( V aTy )
                                                                                                ) TyU ( V aTy )
                                                                                            )
                                                                                        ) TyU
                                                                                        ( Union
                                                                                            ( Union
                                                                                                ( Tcon 0 ( V p_ ) ) TyU ( V aTy )
                                                                                            ) TyU ( V aTy )
                                                                                        )
                                                                                    )
                                                                                ]
                                                                                ( NoBnd () )
                                                                                ( TelBnd TyU
                                                                                    ( bind a
                                                                                        ( TelBnd ( V a )
                                                                                            ( bind _4
                                                                                                ( TelBnd ( V a )
                                                                                                    ( bind _5
                                                                                                        ( NoBnd () )
                                                                                                    )
                                                                                                )
                                                                                            )
                                                                                        )
                                                                                    )
                                                                                )
                                                                            )
                                                                        )
                                                                        ( Same
                                                                            ( TConF "Id"
                                                                                [ V aTy
                                                                                , C ( V xb )
                                                                                    ( Union ( V aTy ) TyU
                                                                                        ( Union
                                                                                            ( Union
                                                                                                ( Tcon 0 ( V p_ ) ) TyU ( V aTy )
                                                                                            ) TyU ( V aTy )
                                                                                        )
                                                                                    )
                                                                                , C ( V xb )
                                                                                    ( Union ( V aTy ) TyU
                                                                                        ( Union
                                                                                            ( Union
                                                                                                ( Tcon 0 ( V p_ ) ) TyU ( V aTy )
                                                                                            ) TyU ( V aTy )
                                                                                        )
                                                                                    )
                                                                                ]
                                                                                ( NoBnd () )
                                                                                ( TelBnd TyU
                                                                                    ( bind a
                                                                                        ( TelBnd ( V a )
                                                                                            ( bind _4
                                                                                                ( TelBnd ( V a )
                                                                                                    ( bind _5
                                                                                                        ( NoBnd () )
                                                                                                    )
                                                                                                )
                                                                                            )
                                                                                        )
                                                                                    )
                                                                                )
                                                                            )
                                                                            ( Info Nothing [] ) TyU
                                                                            ( App
                                                                                ( App
                                                                                    ( App
                                                                                        ( TConF "Id" []
                                                                                            ( TelBnd TyU
                                                                                                ( bind a
                                                                                                    ( TelBnd ( V a )
                                                                                                        ( bind _4
                                                                                                            ( TelBnd ( V a )
                                                                                                                ( bind _5
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
                                                                                                        ( bind _4
                                                                                                            ( TelBnd ( V a )
                                                                                                                ( bind _5
                                                                                                                    ( NoBnd () )
                                                                                                                )
                                                                                                            )
                                                                                                        )
                                                                                                    )
                                                                                                )
                                                                                            )
                                                                                        ) ( V aTy )
                                                                                    ) ( V yb )
                                                                                ) ( V xb )
                                                                            )
                                                                        )
                                                                    )
                                                                )
                                                            ] ( An Nothing )
                                                        )
                                                        ( Same
                                                            ( App
                                                                ( App
                                                                    ( App
                                                                        ( TConF "Id" []
                                                                            ( TelBnd TyU
                                                                                ( bind a
                                                                                    ( TelBnd ( V a )
                                                                                        ( bind _4
                                                                                            ( TelBnd ( V a )
                                                                                                ( bind _5
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
                                                                                        ( bind _4
                                                                                            ( TelBnd ( V a )
                                                                                                ( bind _5
                                                                                                    ( NoBnd () )
                                                                                                )
                                                                                            )
                                                                                        )
                                                                                    )
                                                                                )
                                                                            )
                                                                        ) ( V aTy )
                                                                    ) ( V aTy )
                                                                ) ( V aTy )
                                                            )
                                                            ( Info Nothing [] ) TyU
                                                            ( App
                                                                ( App
                                                                    ( App
                                                                        ( TConF "Id" []
                                                                            ( TelBnd TyU
                                                                                ( bind a
                                                                                    ( TelBnd ( V a )
                                                                                        ( bind _4
                                                                                            ( TelBnd ( V a )
                                                                                                ( bind _5
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
                                                                                        ( bind _4
                                                                                            ( TelBnd ( V a )
                                                                                                ( bind _5
                                                                                                    ( NoBnd () )
                                                                                                )
                                                                                            )
                                                                                        )
                                                                                    )
                                                                                )
                                                                            )
                                                                        ) ( V aTy )
                                                                    ) ( V y )
                                                                ) ( V x )
                                                            )
                                                        )
                                                    )
                                                )
                                            )
                                        )
                                    )
                                )
                            )
                        )
                    , Pi TyU
                        ( bind aTy
                            ( Pi ( V aTy )
                                ( bind xt
                                    ( Pi ( V aTy )
                                        ( bind yt
                                            ( Pi
                                                ( App
                                                    ( App
                                                        ( App
                                                            ( TConF "Id" []
                                                                ( TelBnd TyU
                                                                    ( bind a
                                                                        ( TelBnd ( V a )
                                                                            ( bind _
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
                                                                            ( bind _
                                                                                ( TelBnd ( V a )
                                                                                    ( bind _1
                                                                                        ( NoBnd () )
                                                                                    )
                                                                                )
                                                                            )
                                                                        )
                                                                    )
                                                                )
                                                            ) ( V aTy )
                                                        ) ( V xt )
                                                    ) ( V yt )
                                                )
                                                ( bind _
                                                    ( App
                                                        ( App
                                                            ( App
                                                                ( TConF "Id" []
                                                                    ( TelBnd TyU
                                                                        ( bind a
                                                                            ( TelBnd ( V a )
                                                                                ( bind _1
                                                                                    ( TelBnd ( V a )
                                                                                        ( bind _2
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
                                                                                ( bind _1
                                                                                    ( TelBnd ( V a )
                                                                                        ( bind _2
                                                                                            ( NoBnd () )
                                                                                        )
                                                                                    )
                                                                                )
                                                                            )
                                                                        )
                                                                    )
                                                                ) ( V aTy )
                                                            ) ( V yt )
                                                        ) ( V xt )
                                                    )
                                                )
                                            )
                                        )
                                    )
                                )
                            )
                        )
                    )
                )
            ]
        )
    , PartialModule
        { tCons = fromList
            [
                ( "Id"
                , TelBnd TyU
                    ( <a1> TelBnd V 0 @ 0
                        ( <_3> TelBnd V 1 @ 0 ( <_5> NoBnd () ) )
                    )
                )
            ]
        , dCons = fromList
            [
                ( "Id"
                , fromList
                    [
                        ( "Refl"
                        , TelBnd TyU
                            ( <a7> TelBnd V 0 @ 0
                                ( <x9> NoBnd [ V 1 @ 0, V 0 @ 0, V 0 @ 0 ] )
                            )
                        )
                    ]
                )
            ]
        , refDefs = fromList
            [
                ( "sym"
                , let
                    ( _
                    , _1
                    , _2
                    , _3
                    , _4
                    , _5
                    , a
                    , aTy
                    , aTy1
                    , ab
                    , p_
                    , x
                    , x1
                    , xb
                    , xy
                    , y
                    , yb
                    ) =
                    ( s2n "_"
                    , s2n "_1"
                    , s2n "_2"
                    , s2n "_3"
                    , s2n "_4"
                    , s2n "_5"
                    , s2n "a"
                    , s2n "aTy"
                    , s2n "aTy1"
                    , s2n "ab"
                    , s2n "p_"
                    , s2n "x"
                    , s2n "x1"
                    , s2n "xb"
                    , s2n "xy"
                    , s2n "y"
                    , s2n "yb"
                    ) in Fun
                    ( bind
                        ( _, aTy )
                        ( Fun
                            ( bind
                                ( _1, x )
                                ( Fun
                                    ( bind
                                        ( _2, y )
                                        ( Fun
                                            ( bind
                                                ( _3, xy )
                                                ( C
                                                    ( Case
                                                        [ V x
                                                        , V y
                                                        , C ( V xy )
                                                            ( Same
                                                                ( App
                                                                    ( App
                                                                        ( App
                                                                            ( TConF "Id" []
                                                                                ( TelBnd TyU
                                                                                    ( bind a
                                                                                        ( TelBnd ( V a )
                                                                                            ( bind _4
                                                                                                ( TelBnd ( V a )
                                                                                                    ( bind _5
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
                                                                                            ( bind _4
                                                                                                ( TelBnd ( V a )
                                                                                                    ( bind _5
                                                                                                        ( NoBnd () )
                                                                                                    )
                                                                                                )
                                                                                            )
                                                                                        )
                                                                                    )
                                                                                )
                                                                            ) ( V aTy )
                                                                        ) ( V x )
                                                                    ) ( V y )
                                                                )
                                                                ( Info Nothing [] ) TyU
                                                                ( App
                                                                    ( App
                                                                        ( App
                                                                            ( TConF "Id" []
                                                                                ( TelBnd TyU
                                                                                    ( bind a
                                                                                        ( TelBnd ( V a )
                                                                                            ( bind _4
                                                                                                ( TelBnd ( V a )
                                                                                                    ( bind _5
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
                                                                                            ( bind _4
                                                                                                ( TelBnd ( V a )
                                                                                                    ( bind _5
                                                                                                        ( NoBnd () )
                                                                                                    )
                                                                                                )
                                                                                            )
                                                                                        )
                                                                                    )
                                                                                )
                                                                            ) ( V aTy )
                                                                        ) ( V aTy )
                                                                    ) ( V aTy )
                                                                )
                                                            )
                                                        ]
                                                        [ Match
                                                            ( bind
                                                                [ PVar xb
                                                                , PVar yb
                                                                , Pat "Refl"
                                                                    [ PVar aTy1
                                                                    , PVar ab
                                                                    ] p_
                                                                ]
                                                                ( C
                                                                    ( C
                                                                        ( App
                                                                            ( C
                                                                                ( App
                                                                                    ( DConF "Refl" []
                                                                                        ( "Id"
                                                                                        , TelBnd TyU
                                                                                            ( bind a
                                                                                                ( TelBnd ( V a )
                                                                                                    ( bind x1
                                                                                                        ( NoBnd
                                                                                                            [ V a
                                                                                                            , V x1
                                                                                                            , V x1
                                                                                                            ]
                                                                                                        )
                                                                                                    )
                                                                                                )
                                                                                            )
                                                                                        )
                                                                                        ( TelBnd TyU
                                                                                            ( bind a
                                                                                                ( TelBnd ( V a )
                                                                                                    ( bind x1
                                                                                                        ( NoBnd () )
                                                                                                    )
                                                                                                )
                                                                                            )
                                                                                        )
                                                                                        ( TelBnd TyU
                                                                                            ( bind a
                                                                                                ( TelBnd ( V a )
                                                                                                    ( bind _4
                                                                                                        ( TelBnd ( V a )
                                                                                                            ( bind _5
                                                                                                                ( NoBnd () )
                                                                                                            )
                                                                                                        )
                                                                                                    )
                                                                                                )
                                                                                            )
                                                                                        )
                                                                                    ) ( V aTy1 )
                                                                                )
                                                                                ( Pi
                                                                                    ( Union ( V aTy1 ) TyU
                                                                                        ( Union
                                                                                            ( Union
                                                                                                ( Tcon 0 ( V p_ ) ) TyU ( V aTy )
                                                                                            ) TyU ( V aTy )
                                                                                        )
                                                                                    )
                                                                                    ( bind x1
                                                                                        ( TConF "Id"
                                                                                            [ Union ( V aTy1 ) TyU
                                                                                                ( Union
                                                                                                    ( Union
                                                                                                        ( Tcon 0 ( V p_ ) ) TyU ( V aTy )
                                                                                                    ) TyU ( V aTy )
                                                                                                )
                                                                                            , V x1
                                                                                            , V x1
                                                                                            ]
                                                                                            ( NoBnd () )
                                                                                            ( TelBnd TyU
                                                                                                ( bind a
                                                                                                    ( TelBnd ( V a )
                                                                                                        ( bind _4
                                                                                                            ( TelBnd ( V a )
                                                                                                                ( bind _5
                                                                                                                    ( NoBnd () )
                                                                                                                )
                                                                                                            )
                                                                                                        )
                                                                                                    )
                                                                                                )
                                                                                            )
                                                                                        )
                                                                                    )
                                                                                )
                                                                            )
                                                                            ( C ( V ab )
                                                                                ( Union ( V aTy1 ) TyU
                                                                                    ( Union
                                                                                        ( Union
                                                                                            ( Tcon 0 ( V p_ ) ) TyU ( V aTy )
                                                                                        ) TyU ( V aTy )
                                                                                    )
                                                                                )
                                                                            )
                                                                        )
                                                                        ( TConF "Id"
                                                                            [ V aTy
                                                                            , C
                                                                                ( Union ( V ab )
                                                                                    ( Tcon 0 ( V p_ ) )
                                                                                    ( Union
                                                                                        ( Union ( V ab )
                                                                                            ( Union
                                                                                                ( Tcon 0 ( V p_ ) ) TyU
                                                                                                ( Tcon 0 ( V p_ ) )
                                                                                            )
                                                                                            ( Union
                                                                                                ( Tcon 1 ( V p_ ) )
                                                                                                ( Union
                                                                                                    ( Tcon 0 ( V p_ ) ) TyU
                                                                                                    ( Tcon 0 ( V p_ ) )
                                                                                                ) ( V xb )
                                                                                            )
                                                                                        )
                                                                                        ( Tcon 0 ( V p_ ) ) ( V xb )
                                                                                    )
                                                                                )
                                                                                ( Union
                                                                                    ( Union ( V aTy1 ) TyU
                                                                                        ( Union
                                                                                            ( Union
                                                                                                ( Tcon 0 ( V p_ ) ) TyU ( V aTy )
                                                                                            ) TyU ( V aTy )
                                                                                        )
                                                                                    ) TyU
                                                                                    ( Union
                                                                                        ( Union
                                                                                            ( Tcon 0 ( V p_ ) ) TyU ( V aTy )
                                                                                        ) TyU ( V aTy )
                                                                                    )
                                                                                )
                                                                            , C
                                                                                ( Union ( V ab )
                                                                                    ( Tcon 0 ( V p_ ) )
                                                                                    ( Union
                                                                                        ( Union ( V ab )
                                                                                            ( Union
                                                                                                ( Tcon 0 ( V p_ ) ) TyU
                                                                                                ( Tcon 0 ( V p_ ) )
                                                                                            )
                                                                                            ( Union
                                                                                                ( Tcon 1 ( V p_ ) )
                                                                                                ( Union
                                                                                                    ( Tcon 0 ( V p_ ) ) TyU
                                                                                                    ( Tcon 0 ( V p_ ) )
                                                                                                ) ( V xb )
                                                                                            )
                                                                                        )
                                                                                        ( Tcon 0 ( V p_ ) ) ( V xb )
                                                                                    )
                                                                                )
                                                                                ( Union
                                                                                    ( Union ( V aTy1 ) TyU
                                                                                        ( Union
                                                                                            ( Union
                                                                                                ( Tcon 0 ( V p_ ) ) TyU ( V aTy )
                                                                                            ) TyU ( V aTy )
                                                                                        )
                                                                                    ) TyU
                                                                                    ( Union
                                                                                        ( Union
                                                                                            ( Tcon 0 ( V p_ ) ) TyU ( V aTy )
                                                                                        ) TyU ( V aTy )
                                                                                    )
                                                                                )
                                                                            ]
                                                                            ( NoBnd () )
                                                                            ( TelBnd TyU
                                                                                ( bind a
                                                                                    ( TelBnd ( V a )
                                                                                        ( bind _4
                                                                                            ( TelBnd ( V a )
                                                                                                ( bind _5
                                                                                                    ( NoBnd () )
                                                                                                )
                                                                                            )
                                                                                        )
                                                                                    )
                                                                                )
                                                                            )
                                                                        )
                                                                    )
                                                                    ( Same
                                                                        ( TConF "Id"
                                                                            [ V aTy
                                                                            , C ( V xb )
                                                                                ( Union ( V aTy ) TyU
                                                                                    ( Union
                                                                                        ( Union
                                                                                            ( Tcon 0 ( V p_ ) ) TyU ( V aTy )
                                                                                        ) TyU ( V aTy )
                                                                                    )
                                                                                )
                                                                            , C ( V xb )
                                                                                ( Union ( V aTy ) TyU
                                                                                    ( Union
                                                                                        ( Union
                                                                                            ( Tcon 0 ( V p_ ) ) TyU ( V aTy )
                                                                                        ) TyU ( V aTy )
                                                                                    )
                                                                                )
                                                                            ]
                                                                            ( NoBnd () )
                                                                            ( TelBnd TyU
                                                                                ( bind a
                                                                                    ( TelBnd ( V a )
                                                                                        ( bind _4
                                                                                            ( TelBnd ( V a )
                                                                                                ( bind _5
                                                                                                    ( NoBnd () )
                                                                                                )
                                                                                            )
                                                                                        )
                                                                                    )
                                                                                )
                                                                            )
                                                                        )
                                                                        ( Info Nothing [] ) TyU
                                                                        ( App
                                                                            ( App
                                                                                ( App
                                                                                    ( TConF "Id" []
                                                                                        ( TelBnd TyU
                                                                                            ( bind a
                                                                                                ( TelBnd ( V a )
                                                                                                    ( bind _4
                                                                                                        ( TelBnd ( V a )
                                                                                                            ( bind _5
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
                                                                                                    ( bind _4
                                                                                                        ( TelBnd ( V a )
                                                                                                            ( bind _5
                                                                                                                ( NoBnd () )
                                                                                                            )
                                                                                                        )
                                                                                                    )
                                                                                                )
                                                                                            )
                                                                                        )
                                                                                    ) ( V aTy )
                                                                                ) ( V yb )
                                                                            ) ( V xb )
                                                                        )
                                                                    )
                                                                )
                                                            )
                                                        ] ( An Nothing )
                                                    )
                                                    ( Same
                                                        ( App
                                                            ( App
                                                                ( App
                                                                    ( TConF "Id" []
                                                                        ( TelBnd TyU
                                                                            ( bind a
                                                                                ( TelBnd ( V a )
                                                                                    ( bind _4
                                                                                        ( TelBnd ( V a )
                                                                                            ( bind _5
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
                                                                                    ( bind _4
                                                                                        ( TelBnd ( V a )
                                                                                            ( bind _5
                                                                                                ( NoBnd () )
                                                                                            )
                                                                                        )
                                                                                    )
                                                                                )
                                                                            )
                                                                        )
                                                                    ) ( V aTy )
                                                                ) ( V aTy )
                                                            ) ( V aTy )
                                                        )
                                                        ( Info Nothing [] ) TyU
                                                        ( App
                                                            ( App
                                                                ( App
                                                                    ( TConF "Id" []
                                                                        ( TelBnd TyU
                                                                            ( bind a
                                                                                ( TelBnd ( V a )
                                                                                    ( bind _4
                                                                                        ( TelBnd ( V a )
                                                                                            ( bind _5
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
                                                                                    ( bind _4
                                                                                        ( TelBnd ( V a )
                                                                                            ( bind _5
                                                                                                ( NoBnd () )
                                                                                            )
                                                                                        )
                                                                                    )
                                                                                )
                                                                            )
                                                                        )
                                                                    ) ( V aTy )
                                                                ) ( V y )
                                                            ) ( V x )
                                                        )
                                                    )
                                                )
                                            )
                                        )
                                    )
                                )
                            )
                        )
                    )
                )
            ]
        , refTys = fromList
            [
                ( "sym"
                , let
                    ( _, _1, _2, a, aTy, xt, yt ) =
                    ( s2n "_"
                    , s2n "_1"
                    , s2n "_2"
                    , s2n "a"
                    , s2n "aTy"
                    , s2n "xt"
                    , s2n "yt"
                    ) in Pi TyU
                    ( bind aTy
                        ( Pi ( V aTy )
                            ( bind xt
                                ( Pi ( V aTy )
                                    ( bind yt
                                        ( Pi
                                            ( App
                                                ( App
                                                    ( App
                                                        ( TConF "Id" []
                                                            ( TelBnd TyU
                                                                ( bind a
                                                                    ( TelBnd ( V a )
                                                                        ( bind _
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
                                                                        ( bind _
                                                                            ( TelBnd ( V a )
                                                                                ( bind _1
                                                                                    ( NoBnd () )
                                                                                )
                                                                            )
                                                                        )
                                                                    )
                                                                )
                                                            )
                                                        ) ( V aTy )
                                                    ) ( V xt )
                                                ) ( V yt )
                                            )
                                            ( bind _
                                                ( App
                                                    ( App
                                                        ( App
                                                            ( TConF "Id" []
                                                                ( TelBnd TyU
                                                                    ( bind a
                                                                        ( TelBnd ( V a )
                                                                            ( bind _1
                                                                                ( TelBnd ( V a )
                                                                                    ( bind _2
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
                                                                            ( bind _1
                                                                                ( TelBnd ( V a )
                                                                                    ( bind _2
                                                                                        ( NoBnd () )
                                                                                    )
                                                                                )
                                                                            )
                                                                        )
                                                                    )
                                                                )
                                                            ) ( V aTy )
                                                        ) ( V yt )
                                                    ) ( V xt )
                                                )
                                            )
                                        )
                                    )
                                )
                            )
                        )
                    )
                )
            ]
        }
    )

            ) ( V aTy26 )
        ) ( V yb57 )
    ) ( V xb56 )