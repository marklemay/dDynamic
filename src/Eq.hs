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

    (Case lscrut ann bndlbranchs, Case rscrut _ bndrbranchs) | length bndlbranchs == length bndrbranchs  -> do
      scrut <- eq lscrut rscrut
      
      --TODO: order of cases will be relevent for equality!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
      branchs <- mapM (\ (Match lname bndlBranch, Match rname bndrBranch) -> do
        guard $ lname == rname
        -- TODO this breakes typing aspect of the ctx
        (lparams, lBranch) <- unbind bndlBranch
        (rparams, rBranch) <- unbind bndrBranch
        
        guard $ length lparams == length rparams
        
        branch <- eq lBranch $ substs (fmap (\ (lv,rv) -> (rv, V lv) ) $ zip lparams rparams) rBranch
        pure $ Match lname $ bind lparams branch
        ) $ zip bndlbranchs bndrbranchs
      pure $ Case scrut ann branchs

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