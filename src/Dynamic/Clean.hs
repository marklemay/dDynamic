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


module Dynamic.Clean where


import GHC.Stack

import  Env
import  Dynamic.Ast
import  Dynamic.Norm
import  Dynamic.Err
import  Dynamic.Erase
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
import Unbound.Generics.LocallyNameless.Alpha
import Unbound.Generics.LocallyNameless.Bind
import Unbound.Generics.LocallyNameless.Embed
import Unbound.Generics.LocallyNameless.Ignore
import Unbound.Generics.LocallyNameless.Internal.Fold (foldMapOf, toListOf)
import Unbound.Generics.LocallyNameless.Name
import Unbound.Generics.LocallyNameless.Rebind
import Unbound.Generics.LocallyNameless.Rec
import Unbound.Generics.LocallyNameless.Shift
import Unbound.Generics.LocallyNameless.Subst
import Control.Monad.Except
import Unbound.Generics.LocallyNameless.Unsafe (unsafeUnbind)

import Data.Foldable
import UnboundHelper
import Control.Monad.Reader (ReaderT, MonadReader(ask))
import Control.Monad.State
import Control.Monad.Identity
import Control.Monad.Writer
-- import StdLib (n, s, nat, add, rep, head, stdlib)
import Helper
import AlphaShow
import Control.Applicative
import PreludeHelper



-- | a good defualt to remove unneeded cast tys
cl :: (Fresh m, WithDynDefs m) => Term -> m Term
cl e = clean e eq

clModule m = cleanModule m eq

--TODO can save intermediate nonterminations
-- | remove unneeded cast tys
-- clean :: 
--   HasCallStack => 
--   Fresh m => 
--   Term -> (Term -> Term -> m Bool) -> m Term
clean :: (Fresh m, WithDynDefs m) =>
  Term -> (Term -> Term -> m Bool) -> m Term
clean (Fun bndbod an) eq = do
  (p, bod) <- unbind bndbod
  bod' <- clean bod eq
  pure $ Fun (bind p bod') an

clean (App f a an) eq = do
  f' <- clean f eq
  a' <- clean a eq
  pure $ App f' a' an
clean (Pi aTy bndbod) eq = do
  aTy' <- clean aTy eq
  (p, bod) <- unbind bndbod
  bod' <- clean bod eq
  pure $ Pi aTy' $ bind p bod'
clean (TConF tCName args an) eq = do
  args' <- mapM (\e -> clean e eq) args
  pure $ TConF tCName args' an
clean (DConF dCName args an) eq = do
  args' <- mapM (\e -> clean e eq) args
  pure $ DConF dCName args' an

clean (Case scruts anmotive branch msr an) eq = do
  scruts' <- mapM (\e -> clean e eq) scruts
  branch' <- forM branch $ \ (Match bndbod) -> do
    (p, (assigns, ebod)) <- unbind bndbod
    let Right ebod' = ebod
    ebod'' <- clean ebod' eq
    pure $ Match $ bind p (assigns, Right ebod'')
  pure $ Case scruts' anmotive branch' msr an

clean (Csym u p bndty an) eq = do -- TODO clean bndty?
  u' <- clean u eq
  pure $ Csym u' p bndty an
clean (C u info l wht r) eq = do
  u' <- clean u eq
  l' <- clean l eq
  r' <- clean r eq
  -- TODO these don't actually seem to do that well
  -- l' <- normClean l
  -- r' <- normClean r

  b <- l' `eq` r'
  case b of
    True -> pure $ u'
    False -> do
      -- logg "clean"

      wht' <- whnf wht -- ieadlly do more, but better than nothing
      -- if wht' /= wht
      --   then do
      --     logg "clean,"
      --     -- logg $ e wht
      --     -- logg $ e wht'
      --     loggg $ lfullshow wht
      --     loggg $ lfullshow wht'
      --     pure ()
      --   else pure ()


  -- wht' <- norm pure pure wht -- ieadlly do more, but better than nothing
      -- wht' <- normClean wht -- ok to be wild over the untyped fragment
      -- wht' <- pure wht
      pure $ C u' info l' wht' r'

clean const _ = pure const


-- cleanModule :: 
--   HasCallStack => 
--   Fresh m => 
--   Module -> 
--   (Term -> Term -> m Bool) -> 
--     m Module
cleanModule (Module ddefs (DefCtx trmdefs) vMap) eq = do
  trmdefs' <- forM trmdefs $ \ def -> clean def eq
  ddefs' <- forM ddefs $ \ e -> cleanDataDef e eq
  pure (Module ddefs' (DefCtx trmdefs') vMap)

-- cleanModule :: 
--   HasCallStack => 
--   Fresh m => 
--   (Map TCName DataDef, Map Var (Term, Ty)) -> 
--   (Term -> Term -> m Bool) -> 
--     m (Map TCName DataDef, Map Var (Term, Ty))
-- cleanModule (m@(ddefs,trmdefs)) eq = do
--   trmdefs' <- forM trmdefs $ \ (def,ty) -> do
--     def' <- clean def eq
--     ty' <- clean ty eq
--     pure (def', ty')
--   ddefs' <- forM ddefs $ \ e -> cleanDataDef e eq
--   pure (ddefs', trmdefs')

-- cleanDataDef :: 
--   HasCallStack => 
--   Fresh m => 
--   DataDef -> 
--   (Term -> Term -> m Bool) -> 
--     m DataDef
cleanDataDef (DataDef tConTel dataCons) eq = do
  tConTel' <- tmapM (\ty -> clean ty eq) pure tConTel
  dataCons' <- forM dataCons $ tmapM (\ty -> clean ty eq) (mapM (\ ty -> clean ty eq))
  pure $ DataDef tConTel' dataCons'


eq :: (Fresh f, WithDynDefs f) => Term -> Term -> f Bool
eq l r | l == r = pure True
eq l r = do
  l' <- whnf l
  r' <- whnf r
  case (l', r') of
    _ | l' == r' -> pure True

    -- TODO a little dangourous? TODO should probalby be properly taken care of Csym in norm or only look at the "why" arg 
    ((Csym lu  _ _ _), r') ->  lu `eq` r'
    (l', (Csym ru  _ _ _)) ->  l' `eq` ru

    (Fun bndlBod _,  Fun bndrBod _) -> do
      ((lselfName, laName), lBod) <- unbind bndlBod
      ((rselfName, raName), rBod) <- unbind bndlBod
      
      eq lBod $ subst rselfName (V lselfName noAn) $ subst raName (V laName noAn) rBod
    
    (App lf la _, App rf ra _) -> do
      f <- eq lf rf
      a <- eq la ra
      pure $ f && a
    
    -- TODO check against the other constructors
    
    (TConF lname largs _ , TConF rname rargs _ ) | lname == rname && length largs == length rargs -> do
      args <- mapM (\(l,r) -> l `eq` r) $ zip largs rargs
      pure $ all id args

    (DConF lname largs _ , DConF rname rargs _ ) | lname == rname && length largs == length rargs -> do
      args <- mapM (\(l,r) -> l `eq` r) $ zip largs rargs
      pure $ all id args

    _ -> pure False



-- cleann e = clean e 
-- TODO can be overly clever and thread through a logging monad to collect all the warnings?


