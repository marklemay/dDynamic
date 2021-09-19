{-# LANGUAGE FlexibleContexts #-}

module Eq where

import Unbound.Generics.LocallyNameless
import GHC.Generics (Generic)
import Data.Typeable (Typeable)


import Data.Map (Map)
import qualified Data.Map as Map

import Data.Monoid (Any(..))
import Control.Applicative (Alternative, Applicative(..), (<$>))
import Unbound.Generics.LocallyNameless.Internal.Fold (foldMapOf, toListOf)

import Control.Monad.Except (catchError, MonadError(throwError))
import Control.Monad (guard)

import Ast
import UnboundHelper

import Env
import Norm
import Control.Monad.Reader (MonadReader)
import Control.Monad



--TODO: better type sig?
-- Exp -> Exp -> m (Either String Exp)
-- then can recover origonal behavour with heper funcs


eq :: (MonadReader ctx m, DefnCtx ctx, Alternative m, Fresh m, MonadError String m)
  => Exp -> Exp -> m Exp
eq l r | l == r  = pure l -- this is subtle and prevents a suprising amount of nontermination
eq l r = do -- TODO: posible subtle bug with nonterminating functions.  Should first check equality on safeWhnf?
  l' <- whnf l
  r' <- whnf r
  case (l', r') of
    -- this catchall will handle Var, and constants
    _ | l' `aeq` r' -> pure l'
    (Fun bndlBod,  Fun bndrBod) -> do
      ((lselfName, laName), lBod) <- unbind bndlBod
      ((rselfName, raName), rBod) <- unbind bndlBod
      -- TODO this breakes typing aspect of the ctx
      eq lBod $ subst rselfName (V lselfName) $ subst raName (V laName) rBod
    
    -- TODO: should this be checking against nuetral terms?
    (lf `App` la, rf `App` ra) -> do
      f <- eq lf rf
      a <- eq la ra
      pure $ f `App` a

    (DCon lname, DCon rname) | lname == rname -> do
      pure $ DCon lname

-- what should be the equational behavior of stuck cases? stuck cases with no branches?
    (Case lscruts ann bndlbranchs, Case rscruts _ bndrbranchs) 
      | length lscruts == length rscruts && length bndlbranchs == length bndrbranchs -> do 
      scruts <- mapM (\ (l,r) -> eq l r) $ zip lscruts rscruts
      
      --order of cases will be relevent for equality, which is fine
      branchs <- forM (zip bndlbranchs bndrbranchs) $  \ (Match bndlBranch, Match bndrBranch) -> do
        mp <- unbind2 bndlBranch bndrBranch
        case mp of
          Nothing -> throwError $ "mismatched params, " ++ show bndlBranch ++ " =\\= " ++ show bndrBranch 
          Just (lparams, lBranch, rparams, rBranch) -> do
            branch <- eq lBranch rBranch
            pure $ Match $ bind lparams branch
        
      pure $ Case scruts ann undefined --branchs

    (TCon lname, TCon rname) | lname == rname -> 
      pure $ TCon lname
    -- (TCon lname largs, TCon rname rargs) | lname == rname && length largs == length rargs -> do 
    --   -- would be better to look up types for a ty directed eq
    --   args <- mapM (\ (la, ra) -> eq la ra) $ zip largs rargs
    --   pure $ TCon lname args

    (Pi laty bndlbodty, Pi raty bndrbodty) -> do
      aty <- eq laty raty
      (laname, lbodty) <- unbind bndlbodty
      (raname, rbodty) <- unbind bndrbodty
      bodty <- eq lbodty $ subst raname (V laname) rbodty
      pure $ Pi aty $ bind laname bodty

    (l', r') -> throwError $ "not eq '" ++ show l' ++ "' '" ++ show r' ++ "'" --TODO can't quite throw a pretty error


-- TODO type aware eq
-- eqT :: Term -> Term -> Ty -> TcMonad (Term, Ty)
-- eqT l r ty = do trm <- eq l r; pure $ (trm, ty)


-- eqb :: (MonadReader ctx m, DefnCtx ctx, Alternative m, Fresh m, MonadError String m)
--   => Exp -> Exp -> m Bool -- better type sig
-- eqb l r = (do l `eq` r; pure True) `catchError` (\ ('n' : 'o' : 't' : ' ' : 'e' : 'q' : _) -> pure False -- worse impl
--    )
--TODO better with -> m (Maybe Exp)