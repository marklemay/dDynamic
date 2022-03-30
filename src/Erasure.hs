{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DeriveDataTypeable, DeriveGeneric, MultiParamTypeClasses, FlexibleContexts, FlexibleInstances, DeriveFunctor, RankNTypes, LambdaCase  #-}

module Erasure where

import Ast
import Unbound.Generics.LocallyNameless.Bind
import UnboundHelper

-- class Er a where
--   erase :: a -> Exp

-- instance Er Var where
--   erase = V

-- instance Er Exp where
--   erase (u ::: _) = erase u
--   erase (Fun (B (self, x) bod)) = Fun $ B (self, x) $ erase bod
--   erase (Pi a (B x bod)) = Pi (erase a) $ B x $ erase bod
--   erase (f `App` a) = erase f `App` erase a
--   erase (Case scruts _ branches) = Case (erase <$> scruts) noAn $ fmap (\ (Match (B p b)) -> Match (B p $ erase b)) branches
--   erase (Pos _ e _) = erase e
--   erase e = e
-- another thing that would be helped by a visitor