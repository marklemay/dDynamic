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


module Scratch where

import Data.Map (Map)
import qualified Data.Map as Map

import Data.Set (Set)
import qualified Data.Set as Set

import Data.Monoid (Any (..))
import Data.Typeable (Typeable)
import GHC.Generics (Generic)
import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless.Internal.Fold (foldMapOf, toListOf)
import Unbound.Generics.LocallyNameless.Unsafe (unsafeUnbind)

import UnboundHelper
import AlphaShow

type Var = Name Ex

data Ex 
  = TyU
  | As Ex Ex
  | V Var
  deriving (Generic, Typeable)

instance Alpha Ex
instance Subst Ex Ex where
  -- `isvar` identifies the variable case in your AST.
  isvar (V x) = Just (SubstName x)
  isvar _     = Nothing

instance Eq Ex where
  (==) = aeq

instance AlphaLShow Ex
instance Show Ex where
  show = lfullshow

split :: Ex -> Either Var (String, [Ex])
split TyU = Right ("TyU", [])
split (As l r) = Right ("As", [l, r])
split (V x) = Left x

unsplit :: Either Var (String, [Ex]) -> Ex
unsplit (Right ("TyU", [])) = TyU
unsplit (Right ("As", [l, r])) = (As l r)
unsplit (Left x) = V x
unsplit _ = undefined

unifys :: [Ex] -> [Ex] -> Maybe (Map Var Ex)
unifys [] [] = Just $ Map.fromList []
unifys (l:ls) (r:rs) = do
  m <- unify l r
  let ls' = substs (Map.toList m) ls
  let rs' = substs (Map.toList m) rs
  m' <- unifys ls' rs' 
  pure $ m `Map.union` m'
unifys _ _  = Nothing

unify :: Ex -> Ex -> Maybe (Map Var Ex)
unify (split -> (Left x)) r = Just $ Map.fromList [(x,r)]
unify l (split -> (Left x)) = Just $ Map.fromList [(x,l)]
unify (split -> (Right (hl,argsl))) (split -> (Right (hr,argsr))) | hl == hr = unifys argsl argsr
unify _ _  = Nothing

(x,y,z) = (s2n "x",s2n"y",s2n"z")
ex1 = unify (As TyU TyU) (As (V x) (V x))

rewrite :: Ex -> (Ex,Ex) -> [(Ex,Ex)]
rewrite b (inn,out) = case unify b inn of
  Nothing -> []
  Just m -> [(substs (Map.toList m) inn, substs (Map.toList m) out)]
    
ex2 = rewrite (As (V x) (V x)) ((As TyU TyU), TyU)

rewrites1 :: Ex -> [(Ex,Ex)] -> [(Ex,Ex)]
rewrites1 b ls = concat $ map (rewrite b) ls

ex3 = rewrites1 (As (V x) (V x)) [((As TyU TyU), TyU), (As (V z) (As TyU TyU), (V z))]



-- rewrites :: Ex -> [(Ex,Ex)] -> [(Ex,Ex)]
-- rewrites b@(split -> (Right (hl,argsl))) ls = rewrites1 b ls ++ let
--   vv = tryeach (\x -> map snd $ rewrites x ls) argsl
--   in map (unsplit hl) vv
-- rewrites b ls = rewrites1 b ls

tryeach :: (a ->[a]) -> [a] -> [[a]]
tryeach f [] = []
tryeach f [a] = [f a]
tryeach f (h:ls) = map (: ls) (f h) ++ map (h :) (tryeach f ls)

ex4 = tryeach (\x -> [x+100,x+200]) [1,2,3]


-- rewrites1 :: Ex -> (Ex,Ex) -> [(Ex,Ex)]
-- rewrites1 b (inn, out) = rewrite b (inn, out) 
--    ++ (case split b of
--     Left na -> []
--     Right (h,ls) -> let
--         xx = rewrites1 
--       in undefined)


-- allrewrites :: Ex -> [(Ex,Ex)] -> [Ex,Ex,Ex]
-- allrewrites = undefined

-- pairs :: [Ex,Ex] -> [Ex,Ex,Ex]
-- pairs ls = undefined
-- (Map Var Ex)