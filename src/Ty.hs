{-# LANGUAGE DeriveDataTypeable, DeriveGeneric, MultiParamTypeClasses, FlexibleContexts, FlexibleInstances, DeriveFunctor, RankNTypes, LambdaCase  #-}

module Ty where

import GHC.Stack
import Unbound.Generics.LocallyNameless

import Data.Map (Map)
import qualified Data.Map as Map

import Control.Monad.Reader ( forM_, MonadReader(ask) )
import Control.Monad.Except ( forM_, MonadError(throwError, catchError) )

import PreludeHelper
import UnboundHelper hiding (Telescope)
import Helper

import Ast
import Env
import Eq -- TODO: parameterize this over a monadic equality? so different falvors of normaization can be swapped in and out? how would annotations work?

setRegionFrom :: Exp -> TcMonad a -> TcMonad a
setRegionFrom (Pos s e s') m = setRegion s s' $ setRegionFrom e m 
setRegionFrom _ m = m

isTy :: HasCallStack => Term -> TcMonad Term
isTy exp = do (exp', _) <- tyCheck exp TyU; pure exp'

tyInfer :: HasCallStack => Term -> TcMonad (Term, Ty)
tyInfer (Pos s e s') = setRegion s s' $ tyInfer e
tyInfer (V x) =  do
  xTy <- lookupTy x
  pure (V x, xTy)
tyInfer (trm ::: ty) = tyCheck trm ty
tyInfer TyU = pure (TyU, TyU) -- Type in type
tyInfer (Pi aTy bnd) = do
  aTy' <- isTy aTy
  (aName, bod) <- inCtxWith bnd aTy' isTy
  pure (Pi aTy' $ bind aName bod, TyU)

tyInfer (TCon tCName) = do
  targs <- lookupTCName tCName
  ty <- tellAsFun targs (\ () -> pure TyU)
  pure (TCon tCName, ty)
  
tyInfer (f `App` a) = setRegionFrom f $ do
  (f', fty) <- tyInfer f -- implies that tyInfer should return WHNF
  case erasePos fty of -- TODO only needs to erase the positions up to head
    Pi argTy bndbodTy -> do
      (a', _) <- tyCheck a argTy
      pure (f' `App` a', substBind bndbodTy a')
    ty -> throwprettyError $ show f ++ " : " ++ show ty ++ ", does not have function type"

tyInfer (DCon cid) = do
  (tyname, argTel) <- lookupDCName cid
  -- The well formedness of the evironment should have everyhing checked
  ty <- tellAsFun argTel (pure . (TCon tyname `apps`) )
  pure (DCon cid, ty)
 
tyInfer (Case scrutinee (An (Just bndoutTy)) branches) = do
  -- TODO: check motive is WF!
  -- TODO also not the most efficient! only needs to whnf the constructors

  (scrutinee', scrutineeTy) <- tyInfer scrutinee 
  
  -- case scrutinee [scrutineeName: T symbolictyargs => outTy] { }
  ((scrutineeName, symbolictyargs) , outTy) <- unbind bndoutTy
  
  -- logg $ "outTy = " ++ show outTy

  (tCName, scrutTyParams, constructors) <- case asNeu scrutineeTy of
    Just (TCon tCName, scrutTyParams) -> do 
      DataDef paramtys constructors <- lookupDataDef tCName
      infoGuard "missmatchin of type arguments in motive" $ length scrutTyParams == length symbolictyargs
      
      pure (tCName, scrutTyParams, constructors)
    _ -> throwprettyError $ show scrutinee ++ " : " ++ show scrutineeTy ++ " not a data type"

  -- type check each branch
  forM_ (Map.toList constructors)
    (\ (cName, cTel) -> do
      --find branch from deffinition
      bndBranchBod <- infJustM ("could not find " ++ cName++ " constructor branch") $ lookup cName $ fmap (\ (Match name bndBranchBod) -> (name, bndBranchBod)) branches 
      (patternvars, branchBod) <- unbind bndBranchBod 
      
      -- extend the ctx with patternvars taking the types from the constructor teliscope
      -- generate the branchoutput type by substituting the constructor with patternvars for scrutineeName outTy
      -- make sure the branch : branchoutput type by substituting the constructor with xs for scrutineeName outTy
  {-
      logg "..."
      logg $ "cName = " ++ cName
      logg $ "cTel = " ++ show cTel
      logg $ "patternvars = " ++ show patternvars
      logg $ "branchBod = " ++ show branchBod
  -}  
      
      unpacktel cTel patternvars $ \ tyArgsFromC -> do
        let targetBranchTy = substs (zip symbolictyargs tyArgsFromC) $ subst scrutineeName (apps (DCon cName) $ V <$> patternvars) outTy
      {-
        logg $ "tyArgsFromC = " ++ show tyArgsFromC
        logg $ "symbolictyargs = " ++ show symbolictyargs
        logg $ "scrutineeName = " ++ show scrutineeName
        patternvarsTy <- mapM lookupTy patternvars
        logg $ "patternvarsTy = " ++ show patternvarsTy
        
        logg $ "... = " ++ show targetBranchTy
        
        --inftybranchBod <- tyInfer branchBod
        --logg $ "inftybranchBod = " ++ show inftybranchBod

  -}
        tyCheck branchBod targetBranchTy
    )
  -- NOTE: there will be no warning if additional spurous pattern matches are made

  -- now substitute to get the final type
  pure (Case scrutinee' (An (Just bndoutTy)) branches , substs (zip symbolictyargs scrutTyParams) $ subst scrutineeName scrutinee outTy)


tyInfer (Solve (An (Just ty))) = do
  ty' <- isTy ty
  -- TODO: if solution is in ctx consider putting it here
  pure (Solve  (An (Just ty')),ty')
tyInfer trm = do
  -- logg $ "????" 
  throwprettyError $ "couldn't infer " ++ show trm

-- precondition Ty is well formed, but does not need to be in whnf: a user can activate an equality check
tyCheck :: HasCallStack => Term -> Ty -> TcMonad (Term, Ty)
tyCheck (Pos s e s') ty = setRegion s s' $ tyCheck e ty
-- tyCheck e (Pos s ty s') = setRegion s s' $ tyCheck e ty -- this could be a secondary component of a good error message
tyCheck e (Pos _ ty _) = tyCheck e ty
tyCheck (Solve _) ty = do
  -- TODO: check annotation for consistency
  pure (Solve (An (Just ty)), ty)
  
tyCheck (Fun bndbndbod) fullty@(Pi argTy bndBodTy) = do
  -- TODO: confirm annotation matches, if it existes
  (argNamePi, bodTy) <- unbind bndBodTy
  ((selfName,argName), bod) <- unbind bndbndbod
  
  extendCtx selfName fullty $ extendCtx argName argTy $ tyCheck bod $ subst argNamePi (V argName) bodTy

  pure (Fun bndbndbod, fullty)-- TODO: could probably pass around normalizations slightly better
  

tyCheck (Case scrutinee (An Nothing) branches) fullty = do -- only infer non dependent elimination

  (scrutinee', scrutineeTy) <- tyInfer scrutinee 
  
  -- ((symbolictyargs, scrutineeName) , outTy) <- unbind bndoutTy
  
--  logg $ "outTy = " ++ show outTy

  (tCName, scrutTyParams,  constructors) <- case asNeu scrutineeTy of
    Just (TCon tCName, scrutTyParams) -> do 
      DataDef paramtys constructors <- lookupDataDef tCName
      -- guard $ length scrutTyParams == length symbolictyargs
      
      pure (tCName, scrutTyParams, constructors)
    _ -> throwprettyError $ show scrutinee ++ " : " ++ show scrutineeTy ++ " not a data type"

  -- type check each branch
  forM_ (Map.toList constructors) 
    (\ (cName, cTel) -> do
      --find branch from deffinition
      bndBranchBod <- justM $ lookup cName $ fmap (\ (Match name bndBranchBod) -> (name, bndBranchBod)) branches 
      (patternvars, branchBod) <- unbind bndBranchBod 
      
      -- extend the ctx with patternvars taking the types from the constructor teliscope
      -- generate the branchoutput type by substituting the constructor with patternvars for scrutineeName outTy
      -- make sure the branch : branchoutput type by substituting the constructor with xs for scrutineeName outTy
  {-
      logg "..."
      logg $ "cName = " ++ cName
      logg $ "cTel = " ++ show cTel
      logg $ "patternvars = " ++ show patternvars
      logg $ "branchBod = " ++ show branchBod
  -}  
      
      unpacktel cTel patternvars $ \ tyArgsFromC -> tyCheck branchBod fullty
    )
  -- NOTE: there will be no warning if additional spurous pattern matches are made

  -- now substitute to get the final type
  pure (Case scrutinee' (An Nothing) branches , fullty)


tyCheck tm ty = do
  -- logg $ "check meets infer, " ++ show tm
  (trm', ty') <- tyInfer tm
  -- logg $ "inferred, " ++ show ty'
  ty `eq` ty' `catchError` throwprettyError
  -- logg $ "was eq"
  pure (trm', ty')

-- | is the underlieing environment well formed.  throw if not
envWf :: HasCallStack => TcMonad ()
envWf = do
  (env@(TyEnv tyCtx dataCtx defCtx), _) <- ask
  -- logg "mapM_ isTy tyCtx"
  mapM_ isTy tyCtx 
  -- logg "forM_ dataCtx $ ..."
  forM_ dataCtx $ \ (DataDef tyargs constructors) -> do
    unpacktelTy tyargs
    forM_ constructors $ \ constructor -> do
      unpacktel' constructor (`checktel` tyargs)
  -- logg "forM_ defCtx $ .."
  -- forM_ defCtx $ \(trm, ty) -> isTy ty *> tyCheck trm ty
  forM_ defCtx $ \(trm, ty) -> do
    -- logg $  "isTy ty, " ++ show ty
    isTy ty
    -- logg $  "tyCheck trm ty, " ++ show trm
    tyCheck trm ty
  -- logg "cool"
  pure ()

--TODO: where should this live?
unpacktel :: (Subst Term a, Alpha a) => Telescope a -> [Var]
             -> (a -> TcMonad b)
             -> TcMonad b
unpacktel (NoBnd a) [] f = f a 
unpacktel (TelBnd ty bndRestTel) (x : xs) f = extendCtx x ty $ do (x', restTel) <- unbind bndRestTel; unpacktel (subst x' (V x) restTel) xs f
unpacktel tel app _ = throwprettyError $  " applications do not match type, " ++ show tel ++ "~/~" ++ show app


unpacktel' :: (Subst Term a, Alpha a) => Telescope a 
             -> (a -> TcMonad b)
             -> TcMonad b
unpacktel' (NoBnd a) f = f a 
unpacktel' (TelBnd ty bndRestTel) f = do (_ , x)<- inCtxWith bndRestTel ty (`unpacktel'` f); pure x


unpacktelTy :: (Subst Term a, Alpha a) => Telescope a 
             -> TcMonad ()
unpacktelTy (NoBnd a) = pure ()
unpacktelTy (TelBnd ty bndRestTel) = do
  isTy ty
  inCtxWith bndRestTel ty unpacktelTy
  pure ()


checktel :: (Subst Term a, Alpha a) => [Term] -> Telescope a 
             ->  TcMonad ()
checktel [] (NoBnd a) = pure ()
checktel (trm : restTrm) (TelBnd ty bndRestTel) = do
  tyCheck trm ty
  -- (x, restTel) <- unbind bndRestTel
  checktel restTrm $ substBind bndRestTel trm  -- TODO sohlt this be normalizing?
checktel _ _ = throwprettyError " telescope different length"



--for those who have already checked type
substBindTel :: (Subst Term a, Alpha a) => Telescope a 
             -> [Exp]
             -> ([Ty], a)
substBindTel (NoBnd a) [] = ([], a)
substBindTel (TelBnd ty bndRestTel) (arg:rest) = let
  restTel = substBind bndRestTel arg
  (tys, a) = substBindTel restTel rest
  in (ty:tys, a)
