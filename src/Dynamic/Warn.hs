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




-- warningsModule :: 
--   HasCallStack => 
--   Fresh m => Module -> 
--     -- m [(Info, [(Exp, Obs, Exp)])]
--     m [(Info, Exp, Exp)] -- keep it simple for now, TODO: can give much more specific info
-- warningsModule (Module ddefs (DefCtx trmdefs) vMap) = do
--   trmdefs' <- forM trmdefs $ warnings
--   ddefs' <- forM ddefs $ \ (DataDef e a) -> do
--     (e', ()) <- warningsTel e
--     dc <- forM a $ \ tel -> do
--       (a', ee) <- warningsTel tel
--       ee' <- mapM warnings ee
--       pure $ a' ++ concat ee'
--     pure $ e' ++ (concat $  snd <$> Map.toList dc)
--   pure $ (concat $ snd <$> Map.toList ddefs') ++ (concat $ snd <$> Map.toList trmdefs')


-- warningsTel :: (Fresh f, Typeable n, Alpha b) =>
--      Tel n Exp b -> f ([(Info, Exp, Exp)], b)
-- warningsTel (NoBnd a) = pure ([],a)
-- warningsTel (TelBnd aTy bndBod) = do
--   aTy' <- warnings aTy
--   (_, bod) <- unbind bndBod
--   (warnings , a) <- warningsTel bod
--   pure (aTy' ++ warnings, a)



-- warnings :: 
--   HasCallStack => 
--   Fresh m => Exp -> 
--     -- m [(Info, [(Exp, Obs, Exp)])]
--     m [(Info, Exp, Exp)] -- keep it simple for now, TODO: can give much more specific info

-- warnings (Fun bndbod an) = do
--   (p, bod) <- unbind bndbod
--   warnings bod

-- warnings (App f a an) = do
--   f' <- warnings f
--   a' <- warnings a
--   pure $ f' ++ a'
-- warnings (Pi aTy bndbod)  = do
--   aTy' <- warnings aTy 
--   (p, bod) <- unbind bndbod
--   bod' <- warnings bod 
--   pure $ aTy' ++ bod'
-- warnings (TConF _ args an)  = do
--   args' <- mapM warnings args
--   pure $ concat $ args'
-- warnings (DConF _ args an)  = do
--   args' <- mapM warnings args
--   pure $ concat $ args'
-- warnings (Case scruts anmotive branch msr an)  = do
--   scruts' <- mapM warnings scruts
--   branch' <- forM branch $ \ (Match bndbod) -> do
--     (p, (assigns, ebod)) <- unbind bndbod
--     let Right ebod' = ebod
--     warnings ebod'
--   pure $ concat scruts' ++ concat branch'

-- warnings (Csym u p bndty an)  = do -- TODO warnings bndty?
--   warnings u
-- warnings (C u info l wht r)  = do
--   u' <- warnings u 
--   l' <- warnings l 
--   r' <- warnings r 
--   pure $ u' ++ l' ++ r' ++ [(info, l, r)]
-- warnings const = pure []

-- --TODO : build some monadically paremetric recursors?
-- -- traversExp :: 
-- --   Fresh m => Exp -> (Exp -> m a) -> m a 
-- -- a would be like a monoid?

-- grabSame :: 
--   HasCallStack => 
--   Fresh m => Exp -> m [(Exp, Obs, Exp)]
-- grabSame (Same l o r) = pure [(l, o, r)]
-- grabSame (Fun bndBod _) = do
--   (_, bod) <- unbind bndBod
--   grabSame bod
-- grabSame (App f a _) = do
--   f' <- grabSame f
--   a' <- grabSame a
--   pure $ f' ++ a'
-- grabSame (Pi aTy bndBod) = do
--   aTy' <- grabSame aTy
--   (_, bod) <- unbind bndBod
--   bod' <- grabSame bod
--   pure $ aTy' ++ bod'
-- grabSame (TConF _ args _) = do
--   args' <- mapM grabSame args
--   pure $ concat args'
-- grabSame (DConF _ args _) = do
--   args' <- mapM grabSame args
--   pure $ concat args'
-- grabSame (Case scruts _ branches _ _) = do
--   scruts' <- mapM grabSame scruts
--   branches' <- forM branches $ \ (Match bndbod) -> do
--     (p, (assigns, ebod)) <- unbind bndbod
--     let Right ebod' = ebod
--     grabSame ebod'
--   pure $ concat scruts' ++ concat branches'
-- grabSame (V _ _) = pure []
-- grabSame TyU = pure []
-- grabSame e = error $ "unerased expression, " ++ show e



-- grabSame (Same l o r) = pure [(l, o, r)]