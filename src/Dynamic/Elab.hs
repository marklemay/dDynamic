{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
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


module Dynamic.Elab where

import Prelude hiding (head)
  
import GHC.Stack

import Ast
import qualified Env as E
import qualified Dynamic.Ast as C
import qualified Dynamic.Norm as C
import qualified Dynamic.Err as C
import qualified Dynamic.Temp as C
-- import qualified Dynamic.Env as C --TODO clean
import Dynamic.Env
-- import Dynamic.Norm (whnf)

import Data.Map (Map)
import qualified Data.Map as Map

import Data.Set (Set)
import qualified Data.Set as Set

import Unbound.Generics.LocallyNameless
import Control.Monad.Except
import Unbound.Generics.LocallyNameless.Unsafe (unsafeUnbind)

import UnboundHelper



type Ctx = Map Var C.Exp 

elabInf :: HasCallStack => (Fresh m, MonadError C.Err m, WithDynDefs m, WithSourceLoc m) => Exp -> Ctx -> VMap -> m C.Exp
elabInf (Pos s e s') ctx rename = localSources s s' $ elabInf e ctx rename
elabInf (V x) ctx@(Map.lookup x -> Just ty) rename@(Map.lookup x -> Just x') = pure $ C.V x' $ ann ty
elabInf (e ::: ty) ctx rename = do
  ty' <- elabTy ty ctx rename
  elabCast e ty' ctx rename
elabInf TyU ctx rename = pure C.TyU
elabInf (Fun _) ctx rename = throwPrettyError "not supported because of the plan to remove the function annotations"
elabInf (Pi aTy bndBodTy) ctx rename = do
  aTy' <- elabTy aTy ctx rename
  (aName, bodTy) <- unbind bndBodTy
  aName' <- fresh $ s2n $ name2String aName
  bodTy' <- elabTy bodTy (Map.insert aName aTy' ctx) (Map.insert aName aName' rename)
  pure $ C.Pi aTy' $ bind aName' bodTy'
elabInf e@(f `App` a) ctx rename = localSourceRangeFrom f $ do
  -- logg ""
  -- logg "app"
  -- logg f
  f' <- elabInf f ctx rename -- TODO: prehaps better to return the reduncndant Type C.Exp? or be explicit about the post condition
  -- logg f'
  -- f'' <- C.whnfann f'
  fTy <- mapM C.whnf $ C.tyInf f'
  -- logg f''
  case fTy of
    Just (C.Pi aTy bndBodTy) -> do
      a' <- elabCast a aTy ctx rename
      pure $ C.App f' a' $ ann $ substBind bndBodTy a' -- aName' a' bodTy'
    _ -> throwPrettyError $ "application to non func (whnf is not supported yet)" ++ show (C.apparentTy f') ++" :" ++ show e

-- elabInf (TCon tCname) ctx rename = error "still tranistioning TCon TConF"
elabInf (TCon tCname) ctx rename = do
  tel <- getTConnTel tCname
  pure $ C.TConF tCname [] $ ann tel

elabInf (DCon dCName) ctx rename = do
  (tyname, argTel) <- getConsTcon dCName
  pure $ C.DConF dCName [] $ ann (tyname, argTel)

elabInf (Case scrutinee (An (Just bndoutTy)) branches) ctx rename = localSourceRangeFrom scrutinee $ do
  scrutinee' <- elabInf scrutinee ctx rename
  -- scrutinee'' <- C.whnfann scrutinee'

  scrutineeTy <- mapM C.whnf $ C.tyInf scrutinee'

  ((scrutineeName, symbolictyargs), outTy) <- unbind bndoutTy
  -- guard $ length scrutTyParams == length symbolictyargs

  scrutineeName' <- fresh $ s2n $ name2String scrutineeName
  -- symbolictyargs' <- mapM (fresh . s2n . name2String) symbolictyargs

  case scrutineeTy of
    (Just (C.tConPat -> Just (tCName, scrutTyParams))) -> do
            -- logg $ "scrutTyParams = " ++ show scrutTyParams
      C.DataDef paramtys constructors <- getDatadef tCName
      
      --  elaborate the motive
      bndoutTy' <- unpacktel paramtys symbolictyargs (\ () ctx' rename' -> do
        let (Just symbolictyargs') = mapM (\x -> Map.lookup x rename') symbolictyargs
        let (Just symbolictyexps') = mapM (\x -> do x' <- Map.lookup x rename'; ty <- Map.lookup x ctx'; pure $ C.V x' $ ann ty) symbolictyargs
        let symscrutTy = C.tCon tCName symbolictyexps'
        let ctx'' = Map.insert scrutineeName symscrutTy ctx'
        let rename'' = Map.insert scrutineeName scrutineeName' rename'

        outTy' <- elabTy outTy ctx'' rename''
          -- (Map.insert scrutineeName scrutineeName' $ Map.fromList (zip symbolictyargs symbolictyargs') `Map.union` rename) 
        -- pure (outTy', ctx'', rename'')

        pure $ bind (symbolictyargs', scrutineeName') outTy'
       ) ctx rename

      -- logg $ "showbndoutTy' = " ++ show bndoutTy'

      -- let outTy'' = substs (zip symbolictyargs' scrutTyParams) $ subst scrutineeName' scrutinee' outTy'
      -- let outTy'' = substssBind bndoutTy' (scrutTyParams, scrutinee')
      outTy'' <- substssBind' bndoutTy' (scrutTyParams, scrutinee')
      -- logg $ "outTy'' = " ++ show outTy''

      branches' <- forM branches
        (\ (Match cName bndBranchBod) -> --  Match String (Bind [Var] Term)
          case Map.lookup cName constructors of
            Nothing -> throwPrettyError "unknown constructor"
            Just cTel -> do
              (patternvars, branchBod) <- unbind bndBranchBod
              -- logg $ "branchBod = " ++ show branchBod
              -- patternvars' <- mapM (fresh . s2n . name2String) patternvars
              -- let branchBod' = substs 

              -- logg $ "cTel = " ++ show cTel
              -- logg $ "patternvars' = " ++ show patternvars'

              bndBranchBod' <- unpacktel cTel patternvars (\ params ctx' rename' -> do
                let (Just patternvars') = mapM (\x -> Map.lookup x rename') patternvars
                -- logg "-------------"
                -- logg $ "params = " ++ show params
                -- logg $ "ctx' = " ++ show ctx'
                -- logg $ "rename' = " ++ show rename'
                -- logg $ "patternvars' = " ++ show patternvars'
                -- logg $ "symbolictyargs = " ++ show symbolictyargs
                -- need the pattern vars as an [expression] to substitute into the motive
                
                let (Just patternvarsexps') = forM patternvars $ \x -> do
                                                                  x' <- Map.lookup x rename'
                                                                  -- logg $ show x'
                                                                  ty <- Map.lookup x ctx'
                                                                  pure $ C.V x' $ ann ty
                -- logg $ "patternvarsexps' = " ++ show patternvarsexps'

                let pat = C.DConF cName patternvarsexps' $ ann (tCName, NoBnd params)

                -- let bodTy = substssBind bndoutTy' (params, pat)
                bodTy <- substssBind' bndoutTy' (params, pat)

                -- let patternTy = C.TyUU $ C.TCon tCName params
                out <- elabCast branchBod bodTy ctx' rename'

                pure $ bind patternvars' out
                ) ctx rename

              -- logg "finish cName"

              pure $ C.Match cName bndBranchBod'
         )

      pure $ C.Case scrutinee' (C.swapmotivevars bndoutTy') branches' $ ann (tCName, outTy'') 


    Just ty -> throwPrettyError $ "scrut is not a Tcon, "++ show scrutinee' ++ " : " ++ show ty
    Nothing -> throwPrettyError $ "scrut did not typecheck " ++ show scrutinee'

-- if all branches have matching type,
elabInf (Case scrutinee (An Nothing) branches) ctx rename = localSourceRangeFrom scrutinee $ do
  scrutinee' <- elabInf scrutinee ctx rename

  scrutineeTy <- mapM C.whnf $ C.tyInf scrutinee'

  -- ((symbolictyargs, scrutineeName), outTy) <- unbind bndoutTy

  -- scrutineeName' <- fresh $ s2n $ name2String scrutineeName

  case scrutineeTy of
    (Just (C.tConPat -> Just (tCName, scrutTyParams))) -> do
            -- logg $ "scrutTyParams = " ++ show scrutTyParams
      C.DataDef paramtys constructors <- getDatadef tCName
      
      --  elaborate the motive
      -- bndoutTy' <- unpacktel paramtys symbolictyargs (\ () ctx' rename' -> do
      --   let (Just symbolictyargs') = mapM (\x -> Map.lookup x rename') symbolictyargs
      --   let (Just symbolictyexps') = mapM (\x -> do x' <- Map.lookup x rename'; ty <- Map.lookup x ctx'; pure $ C.V x' $ ann ty) symbolictyargs
      --   let symscrutTy = C.tCon tCName symbolictyexps'
      --   let ctx'' = (Map.insert scrutineeName symscrutTy ctx')
      --   let rename'' =  (Map.insert scrutineeName scrutineeName' rename') 

      --   outTy' <- elabTy outTy ctx'' rename''
      --   pure $ bind (symbolictyargs', scrutineeName') $ outTy'
      --  ) ctx rename

      -- outTy'' <- substssBind' bndoutTy' (scrutTyParams, scrutinee')

      branches' <- forM branches
        (\ (Match cName bndBranchBod) -> --  Match String (Bind [Var] Term)
          case Map.lookup cName constructors of
            Nothing -> throwPrettyError "unknown constructor"
            Just cTel -> do
              (patternvars, branchBod) <- unbind bndBranchBod

              bndBranchBod' <- unpacktel cTel patternvars (\ params ctx' rename' -> do
                let (Just patternvars') = mapM (\x -> Map.lookup x rename') patternvars

                
                let (Just patternvarsexps') = forM patternvars $ \x -> do
                                                                  x' <- Map.lookup x rename'
                                                                  ty <- Map.lookup x ctx'
                                                                  pure $ C.V x' $ ann ty

                let pat = C.DConF cName patternvarsexps' $ ann (tCName, NoBnd params)

                out <- elabInf branchBod  ctx' rename'

                pure $ bind patternvars' out
                ) ctx rename
              
              pure $ C.Match cName bndBranchBod'
         )
      -- logg "hey"
      branchtys <- forM branches' $ \ (C.Match _ bndbranch) -> do
          -- moutTy <- C.underBinder bndbranch C.tyInf
          moutTy <- C.underBinder bndbranch C.tyInf  -- $ \e -> do ty <- C.tyInf e; logg ty; pure ty
          
          -- logg moutTy
          case moutTy of
            Nothing -> throwPrettyError "can only infer simple types in case branch"
            Just Nothing -> throwPrettyError "cpuldnt infer type in case branch"
            Just (Just outTy) -> pure outTy
        
      branchtys' <- mapM C.whnf branchtys
      case branchtys' of
        [] -> throwPrettyError "cannot infer type of branchless case"
        outTy : rest -> 
          if all (outTy `aeq`) rest
            then pure $ C.Case scrutinee' (bind (unnamed, replicate (length scrutTyParams) unnamed) outTy) branches' $ ann (tCName, outTy) 
            else throwPrettyError $ "cases have different simple types, " ++ show branchtys'

    Just ty -> throwPrettyError $ "scrut is not a Tcon, "++ show scrutinee' ++ " : " ++ show ty
    Nothing -> throwPrettyError $ "scrut did not typecheck " ++ show scrutinee'

  

-- needed for elaborating modules with function definitions
elabInf (V x) ctx rename = do
  -- logg x
  mty <- getDefnTy' x
  case mty of
    Just (x', ty) ->  pure $ C.V x' $ ann ty
    Nothing -> throwPrettyError "bad var binding or ty binding"
-- elabInf' (V x) src _ rename@(Map.lookup x -> Nothing) = throwError $ C.Msg $ "bad var binding : " ++ show x ++ " " ++ show rename
-- elabInf' (V x) src ctx@(Map.lookup x -> _) _ = throwError $ C.Msg $ "ty binding : " ++ show x ++ " " ++ show ctx
elabInf e ctx rename = throwPrettyError $ "not handled " ++ show e

elabCast :: HasCallStack => (Fresh m, MonadError C.Err m, WithDynDefs m, WithSourceLoc m) => Exp -> C.Ty -> Ctx -> VMap -> m C.Exp
elabCast (Pos s e s') ty  ctx rename = localSources s s' $ elabCast e ty ctx rename
elabCast (Fun bbndBod) ty ctx rename = do
  ty' <-  C.whnf ty
  case ty' of
    (C.Pi aTy bndBodTy) -> do
      -- logg aTy' 
      ((selfName, aName), bod) <- unbind bbndBod
      selfName' <- fresh $ s2n $ name2String selfName
      -- logg $ "selfName' = " ++ show selfName'
      aName' <- fresh $ s2n $ name2String aName
      -- logg $ "aName' = " ++ show aName'

      -- logg bndBodTy
      let ctx' = Map.insert aName aTy $ Map.insert selfName ty' ctx
      -- logg $ "ctx' = " ++ show ctx'
      let rename' = Map.insert aName aName' $ Map.insert selfName selfName' rename
      -- logg $ "rename' = " ++ show rename'
      let outTy = substBind bndBodTy (C.V aName' $ ann aTy)
      -- logg $ "outTy = " ++ show outTy
      --   logg (C.TyUU aTy' $ C.V aName')

      bod' <- elabCast bod outTy ctx' rename'
      -- logg bod'

      pure $ C.Fun (bind (selfName', aName') bod') $ ann (aTy, bndBodTy)
    _ -> throwPrettyError $ "cast non pi to func " ++ show bbndBod ++ "  :  " ++ show ty' -- what if there is some wiggle room? not enough to safely infer a dependent output.


elabCast e ty ctx rename = do
  e' <- elabInf e ctx rename
  r <- askSourceRange
  let ety = C.apparentTy e'
  case r of
    Just r -> pure $ C.C e' ety (C.Same ety (C.initInfo r ety ty) ty) ty --(C.L ty "" C.Base $ C.apparentTy e') 
    _ -> throwPrettyError "no source range when needed" 

elabTy :: (Fresh m, MonadError C.Err m, WithDynDefs m, WithSourceLoc m) => Exp -> Ctx -> VMap -> m C.Exp
elabTy TyU ctx rename = pure C.TyU
elabTy e ctx rename = elabCast e C.TyU ctx rename




elabCastTelUnit :: (Fresh m, MonadError C.Err m, WithDynDefs m, WithSourceLoc m) => [Exp] -> Tel C.Term C.Ty ()
             -> Ctx -> VMap -> m [C.Exp]
elabCastTelUnit [] (NoBnd ()) ctx rename = pure []
elabCastTelUnit (trm : restTrm) (TelBnd ty bndRestTel) ctx rename = do
  cexp <- elabCast trm ty ctx rename
  -- logg "cexp"
  -- logg $ lfullshow cexp
  let restTel = substBind bndRestTel cexp
  -- logg "restTel"
  -- logg $ lfullshow restTel
  rest <- elabCastTelUnit restTrm restTel ctx rename 
  pure $ cexp : rest
elabCastTelUnit _ _ _ _ = throwPrettyError " telescope different length"


unpacktel :: (Subst C.Ty a, Alpha a, Fresh m, MonadError C.Err m) => Tel C.Term C.Ty a -> [Var]
             -> (a -> Ctx -> VMap -> m b)
             -> Ctx -> VMap
             -> m b
unpacktel (NoBnd a) [] f ctx rename = f a ctx rename
unpacktel (TelBnd ty bndRestTel) (x : xs) f ctx rename = do
  x' <- fresh $ s2n $ name2String x
  unpacktel (substBind bndRestTel (C.V x' $ ann ty)) xs f (Map.insert x ty ctx) (Map.insert x x' rename)
unpacktel tel ls _ _ _ = error $ "applications do not match type" ++ show tel ++ " " ++ show ls

