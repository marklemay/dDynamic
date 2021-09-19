{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DeriveDataTypeable, DeriveGeneric, MultiParamTypeClasses, FlexibleContexts, FlexibleInstances, DeriveFunctor, RankNTypes, LambdaCase  #-}

--TODO clean up GHC params

module Unification where


import GHC.Stack
import Unbound.Generics.LocallyNameless

import Data.Map (Map)
import qualified Data.Map as Map

import Control.Monad.Reader
import Control.Monad.Except ( forM_, MonadError(throwError, catchError) )

import PreludeHelper
import UnboundHelper hiding (Telescope)
import Helper

import Ast
import Env
import Eq -- TODO: parameterize this over a monadic equality? so different falvors of normaization can be swapped in and out? how would annotations work?


import Norm 

-- unify some numver of iterations
fOUni x ls | x <= 0 = error ".."
fOUni 1 ls = fOUni' ls [] []
fOUni x ls = do
  ans@(env, eqs, unsat) <- fOUni' ls [] []
  case eqs of
    [] -> pure ans
    _ -> do
       (env', eqs', unsat')<- local (\(_,s) -> (env,s)) $ fOUni (x-1) eqs
       pure (env', eqs', unsat ++ unsat')

-- right biased, the right type expression is assumed to be type correct
-- active, stuck, unsat ->  assign, stuck, unsat 
fOUni' :: HasCallStack => [(Exp, Exp,Ty)] -> [(Exp, Exp, Ty)] -> [(Exp, Exp)] -> TcMonad (TyEnv, [(Exp, Exp,Ty)], [(Exp, Exp)] )
fOUni'  ((l, r,_) :ls) stuck unsat | sameHead l r == Just False = fOUni' ls stuck $ (l,r):unsat

fOUni' ((asNeu -> Just (DCon s, args), asNeu -> Just (DCon s', args'),ty):rest) stuck unsat | s == s' && length args == length args' = do
  (_, tel) <- lookupDCName s'
  let neweqs = fmap (\(arg,(arg',ty))-> (arg,arg',ty)) $ zip args $ withTy args' tel
  fOUni' (neweqs++rest) stuck  unsat

fOUni' ((asNeu -> Just (TCon s, args), asNeu -> Just (TCon s', args'),ty):rest) stuck unsat | s == s' && length args == length args' = do
  tel <- lookupTCName s'
  let neweqs = fmap (\(arg,(arg',ty))-> (arg,arg',ty)) $ zip args $ withTy args' tel
  fOUni' (neweqs++rest) stuck unsat

fOUni' (eq@(V x, e, ety):rest) stuck unsat = do
  mx <- lookupDef' x
  case mx of
    Nothing -> local 
      (\(TyEnv tyCtx dataCtx defCtx,s) -> (TyEnv tyCtx  dataCtx $ Map.insert x (e,ety) defCtx,s)) $
        fOUni' rest stuck unsat
    _ -> fOUni' rest (stuck++ [eq]) unsat 

fOUni' (eq@(e, V x, ety):rest) stuck unsat = do
  mx <- lookupDef' x
  case mx of
    Nothing -> local 
      (\(TyEnv tyCtx dataCtx defCtx,s) -> (TyEnv tyCtx  dataCtx $ Map.insert x (e,ety) defCtx,s)) $
        fOUni' rest stuck unsat
    _ -> fOUni' rest (stuck++ [eq]) unsat 

fOUni' (nope:rest) stuck unsat =  fOUni' rest (stuck++ [nope]) unsat --rotate non easy terms to the back

fOUni' [] stuck unsat = do
  stuck' <- mapM (\(l,r,ty) -> do l' <- safeWhnf l; r' <- safeWhnf r; pure (l', r', ty) ) stuck
  if stuck' == stuck -- quite inefficient
    then do (env,_) <- ask; pure (env, stuck', unsat)
    else  fOUni' stuck' [] unsat


ee33 = runTcMonadIo empctx $ fOUni' [(V x, V y, TyU)] [] []
  where
    x = s2n "x"
    y = s2n "y"

-- Map Var (Term, Ty)
--  (TyEnv tyCtx dataCtx defCtx) 
cleanDefCtx' [] defCtx = []
cleanDefCtx' [] defCtx = []


isWhnf :: Exp -> Bool
isWhnf TyU = True
isWhnf (Pi _ _) = True
isWhnf (Fun _ ) = True
isWhnf (asNeu -> Just (TCon _, _)) = True
isWhnf (asNeu -> Just (DCon _, _)) = True
isWhnf _ = False

sameHead :: Exp -> Exp -> Maybe Bool
sameHead TyU TyU = Just True
sameHead (asNeu -> Just (DCon s1, args)) (asNeu -> Just (DCon s2, args')) | s1 == s2 && length args /= length args' = error "len error"
sameHead (asNeu -> Just (TCon s1, args)) (asNeu -> Just (TCon s2, args')) | s1 == s2 && length args /= length args' = error "len error"
sameHead (asNeu -> Just (DCon s1, _)) (asNeu -> Just (DCon s2, _)) | s1 == s2 = Just True
sameHead (asNeu -> Just (TCon s1, _)) (asNeu -> Just (TCon s2, _)) | s1 == s2 = Just True
sameHead (Fun _) (Fun _) = Just True
sameHead (Pi _ _) (Pi _ _) = Just True
sameHead e1 e2 | isWhnf e1 && isWhnf e2 = Just False
sameHead _ _ = Nothing 


withTy :: (Alpha a, Subst Exp a) => [Exp] -> Telescope a -> [(Exp,Ty)]
withTy [] (NoBnd _) = []
withTy (h:t) (TelBnd ty bndrest)  = 
  let rest = substBind bndrest h 
  in (h,ty) : withTy t rest 
withTy _ _ = error "bad arg len"
