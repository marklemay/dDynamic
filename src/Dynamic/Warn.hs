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


module Dynamic.Warn where


import GHC.Stack

import  Env
import  Dynamic.Ast
import  Dynamic.Norm
import  Dynamic.Err
-- import  Dynamic.Temp
-- import qualified Dynamic.Env as C --TODO clean
import Dynamic.Env
-- import Dynamic.Norm (whnf)
import Dynamic.Erase

import Data.Map (Map)
import qualified Data.Map as Map

import Data.Set (Set)
import qualified Data.Set as Set

import Data.Monoid (Any (..))
import Data.Typeable (Typeable)
import GHC.Generics (Generic)
import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless.Internal.Fold (foldMapOf, toListOf)
import Control.Monad.Except
import Unbound.Generics.LocallyNameless.Unsafe (unsafeUnbind)

import UnboundHelper
import Control.Monad.Reader (ReaderT, MonadReader(ask))
import Helper
import AlphaShow
import Control.Applicative
import SourcePos (SourceRange(SourceRange))

-- type Warns = Map SourceRange (Ty,Ty, [(Obs, Exp,Exp)])
type Warns = [(SourceRange, Ty, Ty, Obs, Exp,Exp)]

consolidate :: Warns -> Map SourceRange (Ty,Ty, Map Obs (Exp,Exp))
consolidate [] = Map.empty 
consolidate ((sr, lty, rty, o, le, re) : rest) = let
  rest' = consolidate rest
  in 
  case Map.lookup sr rest' of
    Nothing -> Map.insert sr (lty, rty, Map.fromList [(o, (le, re))]) rest'
    Just (_, _, obs) -> Map.insert sr (lty, rty, Map.insert o (le, re) obs) rest'
-- ls = let
--   m1 = Map.fromList $ fmap (\(sr, lty,rty, o, le, re)-> (sr, (lty,rty, o, le, re))) ls
--   _ = Map.map (\ x -> x ) m1

--   in undefined

warningsModule :: 
  HasCallStack => 
  Fresh m => Module -> 
    -- m [(Info, [(Exp, Obs, Exp)])]
    m Warns
warningsModule (Module ddefs (DefCtx trmdefs) vMap) = do
  trmdefs' <- forM trmdefs $ warnings
  ddefs' <- forM ddefs $ \ (DataDef e a) -> do
    (e', ()) <- warningsTel e
    dc <- forM a $ \ tel -> do
      (a', ee) <- warningsTel tel
      ee' <- mapM warnings ee
      pure $ a' ++ concat ee'
    pure $ e' ++ (concat $  snd <$> Map.toList dc)
  pure $ (concat $ snd <$> Map.toList ddefs') ++ (concat $ snd <$> Map.toList trmdefs')


warningsTel :: (Fresh f, Typeable n, Alpha b) =>
     Tel n Exp b -> f (Warns, b)
warningsTel (NoBnd a) = pure ([],a)
warningsTel (TelBnd aTy bndBod) = do
  aTy' <- warnings aTy
  (_, bod) <- unbind bndBod
  (warnings , a) <- warningsTel bod
  pure (aTy' ++ warnings, a)



warnings :: 
  HasCallStack => 
  Fresh m => Exp -> 
    -- m [(Info, [(Exp, Obs, Exp)])]
    m Warns -- keep it simple for now, TODO: can give much more specific info

warnings (Fun bndbod an) = do
  (p, bod) <- unbind bndbod
  warnings bod

warnings (App f a an) = do
  f' <- warnings f
  a' <- warnings a
  pure $ f' ++ a'
warnings (Pi aTy bndbod)  = do
  aTy' <- warnings aTy 
  (p, bod) <- unbind bndbod
  bod' <- warnings bod 
  pure $ aTy' ++ bod'
warnings (TConF _ args an)  = do
  args' <- mapM warnings args
  pure $ concat $ args'
warnings (DConF _ args an)  = do
  args' <- mapM warnings args
  pure $ concat $ args'
warnings (Case scruts anmotive branch msr an)  = do
  scruts' <- mapM warnings scruts
  branch' <- forM branch $ \ (Match bndbod) -> do
    (p, (assigns, ebod)) <- unbind bndbod
    let Right ebod' = ebod
    warnings ebod'
  pure $ concat scruts' ++ concat branch'

warnings (Csym u p bndty an)  = do -- TODO warnings bndty?
  warnings u
warnings (C u (Info src _ _ _ _) l wht r)  = do
  u' <- warnings u 
  l' <- warnings l -- TODO can eval these better
  r' <- warnings r 
  sw <- grabSame wht src 
  pure $ u' ++ l' ++ r' ++ fmap (\ (el,o,er) -> (src, l, r, o, el, er)) sw
warnings const = pure []

--TODO : build some monadically paremetric recursors?
-- traversExp :: 
--   Fresh m => Exp -> (Exp -> m a) -> m a 
-- a would be like a monoid?

grabSame :: 
  HasCallStack => 
  Fresh m => Exp -> SourceRange -> m [(Exp, Obs, Exp)]
-- grabSame = undefined 
grabSame (Same l (Info src' o _ _ _) r) src | src == src' && e l /= e r = pure [(l, o, r)]
grabSame (Fun bndBod _) src = do
  (_, bod) <- unbind bndBod
  grabSame bod src
grabSame (App f a _) src = do
  f' <- grabSame f src
  a' <- grabSame a src
  pure $ f' ++ a'
grabSame (Pi aTy bndBod) src = do
  aTy' <- grabSame aTy src
  (_, bod) <- unbind bndBod
  bod' <- grabSame bod src
  pure $ aTy' ++ bod'
grabSame (TConF _ args _) src = do
  args' <- mapM (\ arg -> grabSame arg src)args 
  pure $ concat args'
grabSame (DConF _ args _) src = do
  args' <- mapM (\ arg -> grabSame arg src)args 
  pure $ concat args'
grabSame (Case scruts _ branches _ _) src = do
  scruts' <- mapM (\ arg -> grabSame arg src) scruts 
  branches' <- forM branches $ \ (Match bndbod) -> do
    (p, (assigns, ebod)) <- unbind bndbod
    let Right ebod' = ebod
    grabSame ebod' src
  pure $ concat scruts' ++ concat branches'

-- TODO the tinyest bit scetchy
grabSame (C u _ l _ r) src = do
  u' <- grabSame u src
  l' <- grabSame l src
  r' <- grabSame r src
  pure $ u' ++ l' ++ r' 
grabSame (Csym u p bndty an) src = do 
  grabSame u src

grabSame _ _ = pure []



-- grabSame (Same l o r) = pure [(l, o, r)]