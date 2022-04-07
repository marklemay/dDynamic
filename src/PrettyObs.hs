{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}


{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
module PrettyObs where
import Ast
import Parser
import ParserMonad
import Prelude hiding (exp)
import Dynamic.Ast (Obs, ObsAtom (..))
import Helper
-- TODO repl folfer?

-- a bit of a hack
enrichWithPos :: Exp -> (String, Exp)
enrichWithPos e = let
  s = prettyShow False e 0
  Right e' = prettyParse "" s exp
  in (s, e')


-- prettyobs' :: Exp -> Obs -> [String]
-- prettyobs' (asNeu -> Just (V _, args)) (Index i:rest) =  undefined 
-- prettyobs' (asNeu -> Just (_, args)) (Index i:rest) | i < (fromIntegral $ length args) =  prettyobs' $ args !! i