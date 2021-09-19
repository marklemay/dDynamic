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
import Dynamic.Unification
-- import Dynamic.Norm (whnf)
import AlphaShow

import Data.Map (Map)
import qualified Data.Map as Map

import Data.Set (Set)
import qualified Data.Set as Set

import Unbound.Generics.LocallyNameless
import Control.Monad.Except
import Unbound.Generics.LocallyNameless.Unsafe (unsafeUnbind)

import UnboundHelper



type Ctx = Map Var C.Exp

applyTyDefs' :: (Fresh m) => C.Exp -> [(C.Var, C.Path, C.Exp)] -> m [(C.Path, Bind C.Var C.Ty, C.Ty)] -- and the top ty
applyTyDefs' e [] = pure []
applyTyDefs' e ((x, p, withThis):rest) = do
  let e' = subst x withThis e
  rest' <- applyTyDefs' e' rest
  pure $ (p, bind x $ e, e') : rest'

-- TODO better name
addPatternCasts :: (Fresh m) => C.Exp -> TyDefs -> m C.Exp
addPatternCasts e @ (C.tyInf -> Just ty) assumeDefs = do
  ls <- applyTyDefs' ty assumeDefs

  let e' = foldl (\ e (p, bndTy, topTy) -> C.Csym e p bndTy $ ann topTy) e ls
  pure e'


revaddPatternCasts :: (Fresh m) => C.Ty -> TyDefs -> m (C.Ty, [(C.Path, Bind C.Var C.Ty, C.Ty)])
revaddPatternCasts ty assumeDefs = revaddPatternCasts' ty (reverse assumeDefs)

revaddPatternCasts' :: (Fresh m) => C.Ty -> TyDefs -> m (C.Ty, [(C.Path, Bind C.Var C.Ty, C.Ty)])
revaddPatternCasts' ty [] = pure (ty, [])
revaddPatternCasts' ty ((x, p, withThis):rest) = do
  let ty' = subst x withThis ty
  (ty'', rest') <- revaddPatternCasts' ty' rest
  pure $ (ty'', (C.rev p, bind x $ ty, ty) : rest')


--TODO monadicify these Ctx -> VMap -> TyDefs readers
elabInf :: HasCallStack => (Fresh m, MonadError C.Err m, WithDynDefs m, WithSourceLoc m) => Exp -> Ctx -> VMap -> TyDefs -> m C.Exp
elabInf (Pos s e s') ctx rename assumeDefs = localSources s s' $ elabInf e ctx rename assumeDefs
elabInf (V x) ctx@(Map.lookup x -> Just ty) rename@(Map.lookup x -> Just x') assumeDefs = addPatternCasts (C.V x' $ ann ty) assumeDefs
elabInf (e ::: ty) ctx rename assumeDefs = do -- TODO double check all this, perhaps refactor
  ty' <- elabty ty ctx rename assumeDefs  
  (ty'', casts) <- revaddPatternCasts' ty' assumeDefs

  underExp <- elabCast e ty'' ctx rename assumeDefs
  let expWithcast = foldl (\ e (p, bndTy, topTy) -> C.Csym e p bndTy $ ann topTy) underExp casts

  addPatternCasts expWithcast assumeDefs

elabInf TyU ctx rename assumeDefs = pure C.TyU
elabInf (Fun _) ctx rename assumeDefs = throwPrettyError "currently cannot infer the type of a naked function"
elabInf (Pi aTy bndBodTy) ctx rename assumeDefs = do -- TODO  I believe all assumeDefs can be cast in each branch
  aTy' <- elabty aTy ctx rename assumeDefs
  (aName, bodTy) <- unbind bndBodTy
  aName' <- fresh $ s2n $ name2String aName
  bodTy' <- elabty bodTy (Map.insert aName aTy' ctx) (Map.insert aName aName' rename) assumeDefs
  pure $ C.Pi aTy' $ bind aName' bodTy'
elabInf e@(f `App` a) ctx rename assumeDefs = localSourceRangeFrom f $ do
  -- logg ""
  -- logg "app"
  -- logg f
  f' <- elabInf f ctx rename assumeDefs -- TODO: prehaps better to return the reduncndant Type C.Exp? or be explicit about the post condition
  -- logg f'
  -- f'' <- C.whnfann f'
  fTy <- mapM C.whnf $ C.tyInf f'
  -- logg f''
  case fTy of
    Just (C.Pi aTy bndBodTy) -> do
      a' <- elabCast a aTy ctx rename assumeDefs -- assumeDefs have already been applied in aTy

      addPatternCasts (C.App f' a' $ ann $ substBind bndBodTy a') assumeDefs -- still need to cast the output since the uncast term may have been substituted into teh type
    _ -> throwPrettyError $ "application to non func (whnf is not supported yet)" ++ show (C.apparentTy f') ++" :" ++ show e

elabInf (TCon tCname) ctx rename assumeDefs = do  -- don't need to apply assumeDefs here, that will be taken care of in application
  tel <- getTConnTel tCname
  pure $ C.TConF tCname [] $ ann tel

elabInf (DCon dCName) ctx rename assumeDefs = do -- don't need to apply assumeDefs here, that will be taken care of in application
  (tyname, argTel) <- getConsTcon dCName
  pure $ C.DConF dCName [] $ ann (tyname, argTel)

elabInf (Case scrutinees (An (Just tel)) branches) ctx rename assumeDefs = do
  sr <- askSourceRange

  
  -- logg $ "scrutinees = " ++ lfullshow scrutinees
  -- logg $ "branches = " ++ lfullshow branches
  -- logg $ "ctx = " ++ lfullshow ctx -- TODO: some issue here
  -- logg $ "rename = " ++ lfullshow rename
  -- logg $ "assumeDefs = " ++ lfullshow assumeDefs
  -- logg $ "sr = " ++ show sr

  -- resolve the telescope, ath annotation must be present in inference mode, will need to mutually elaberate teh scrutinees

  -- logg $ "scrutinees = " ++ show scrutinees
  -- logg $ "tel = " ++ show tel

  (scrutinees', caseTy, tel') <- checkTelMaybe scrutinees tel Map.empty ctx rename assumeDefs

  -- logg $ "scrutinees' = " ++ show scrutinees'
  -- logg $ "caseTy = " ++ show caseTy
  -- logg $ "tel' = " ++ show tel'
  branches' <- forM branches $ \ (Match bndbod) -> do
    (pats, bod) <- unbind bndbod
    -- logg $ "pats = " ++ show pats
    -- logg $ "pats = " ++ lfullshow pats
    -- logg $ "tel' = " ++ show tel'

    (unzip->(pats',exps'), outTy, eqs, ctx', rename') <- elabCastPats pats tel' ctx rename
    -- logg $ "... "
    -- logg $ "pats' = " ++ show pats'
    -- logg $ "exps' = " ++ show exps'
    -- logg $ "outTy = " ++ show outTy
    -- eqs' <- forM eqs $ \ (l,r,p) -> do
    --   l' <- C.whnf l
    --   r' <- C.whnf r
    --   pure (l',r',p)

    -- logg $ "eqs' = " ++ show eqs'
    -- logg $ "length eqs = " ++ (show $ length eqs)
    -- logg $ "eqs = " ++ (show $ take 1 eqs)
    -- logg $ "... "
    -- logg $ "eqs = " ++ lfullshow eqs -- something is really wrong here!
    -- logg $ "eqs = " ++ show eqs
    
    uni <- fOUni eqs --TODO needs to acount for exterior assumeDefs, to not override those in the nested case

    -- logg $ "uni = " ++ lfullshow uni -- TODO show bug
    -- logg $ "uni = " ++ show uni
    case uni of 
      Right ((fmap (\ (v,e,p) -> (v,p,e))) -> assumeDefs', []) -> do
        


        let assumeDefs'' = assumeDefs ++ assumeDefs' --TODO slightly incorrect?

        (outTy', casts) <- revaddPatternCasts' outTy assumeDefs''

        bod' <- elabCast bod outTy' ctx' rename' assumeDefs''
        let expWithcast = foldl (\ e (p, bndTy, topTy) -> C.Csym e p bndTy $ ann topTy) bod' casts 

        bod'' <- addPatternCasts expWithcast assumeDefs
        pure $ C.Match $ bind pats' (assumeDefs', Right bod'')

        --TODO these cases justify position information for matches and sub patterns
      Right unsolved -> throwPrettyError $ "unification could not solve this branch.   " ++ show pats ++ " unsat by "++ show unsolved -- TODO: how should people get out of this situation?
      Left unsat -> throwPrettyError $ "unification proved that this branch unsat, remove it.   " ++ show pats ++ " unsat by "++ show unsat

  -- TODO check for completeness
  
  addPatternCasts (C.Case scrutinees' (noAn) branches' sr (ann caseTy)) assumeDefs
  

-- needed for elaborating modules with function definitions
elabInf (V x) ctx rename assumeDefs = do -- don't need to apply assumeDefs here, that will be taken care of in application
  -- logg x
  mty <- getDefnTy' x
  case mty of
    Just (x', ty) ->  pure $ C.V x' $ ann ty
    Nothing -> throwPrettyError "bad var binding or ty binding"
-- elabInf' (V x) src _ rename@(Map.lookup x -> Nothing) = throwError $ C.Msg $ "bad var binding : " ++ show x ++ " " ++ show rename
-- elabInf' (V x) src ctx@(Map.lookup x -> _) _ = throwError $ C.Msg $ "ty binding : " ++ show x ++ " " ++ show ctx
elabInf e ctx rename assumeDefs = throwPrettyError $ "not handled " ++ show e

elabCast :: HasCallStack => (Fresh m, MonadError C.Err m, WithDynDefs m, WithSourceLoc m) => Exp -> C.Ty -> Ctx -> VMap -> TyDefs -> m C.Exp
elabCast (Pos s e s') ty  ctx rename assumeDefs = localSources s s' $ elabCast e ty ctx rename assumeDefs
elabCast (Fun bbndBod) ty ctx rename assumeDefs = do
  
  -- logg $ "ty = " ++ show ty
  -- logg $ "ty = " ++ lfullshow ty
  ty' <-  C.whnf ty
  case ty' of
    (C.Pi aTy bndBodTy) -> do
      -- logg aTy' 
      ((selfName, aName), bod) <- unbind bbndBod
      selfName' <- fresh $ s2n $ name2String selfName
      -- logg $ "selfName' = " ++ show selfName'
      aName' <- fresh $ s2n $ name2String aName
      -- logg $ "aName' = " ++ show aName'
     
      -- logg $ "ctx = " ++ lfullshow ctx
      
      -- logg $ "aName = " ++ show aName
      -- logg $ "aTy = " ++ lfullshow aTy
      -- logg $ "selfName = " ++ show selfName
      -- logg $ "ty' = " ++ lfullshow ty'

      -- logg $ "Map.insert selfName ty' ctx = " ++ lfullshow (Map.insert selfName ty' ctx)
      -- logg bndBodTy
      let ctx' = Map.insert aName aTy $ Map.insert selfName ty' ctx
      -- logg $ "ctx' = " ++ lfullshow ctx'
      -- logg $ "ctx' = " ++ show ctx'
      let rename' = Map.insert aName aName' $ Map.insert selfName selfName' rename
      -- logg $ "rename' = " ++ show rename'
      let outTy = substBind bndBodTy (C.V aName' $ ann aTy)
      -- logg $ "outTy = " ++ show outTy
      --   logg (C.TyUU aTy' $ C.V aName')

      bod' <- elabCast bod outTy ctx' rename' assumeDefs
      -- logg bod'

      pure $ C.Fun (bind (selfName', aName') bod') $ ann (aTy, bndBodTy)
    _ -> throwPrettyError $ "cast non pi to func " ++ show bbndBod ++ "  :  " ++ show ty' -- what if there is some wiggle room? not enough to safely infer a dependent output.
-- TODO several other syntaxes
elabCast (Case scrutinee (An Nothing) branches) ty ctx rename assumeDefs = throwPrettyError "not yet supporting case elaboration inference"


elabCast e ty ctx rename assumeDefs = do
  e' <- elabInf e ctx rename assumeDefs
  mr <- askSourceRange
  let ety = C.apparentTy e'
  case mr of
    Just r -> do
      let info@(C.Info _ obs _ _ _) = (C.initInfo r ety ty)
      -- logg $ show ety ++ " =?= " ++ show ty
      pure $ C.C e' info ety (C.Same ety obs ty) ty
    _ -> throwPrettyError "no source range when needed" 

elabty :: (Fresh m, MonadError C.Err m, WithDynDefs m, WithSourceLoc m) => Exp -> Ctx -> VMap -> TyDefs -> m C.Exp
elabty TyU ctx rename assumeDefs = pure C.TyU
elabty e ctx rename assumeDefs = elabCast e C.TyU ctx rename assumeDefs

--TODO capitalize
elabTy :: (Fresh m, MonadError C.Err m, WithDynDefs m, WithSourceLoc m) => Exp -> Ctx -> VMap -> TyDefs -> m C.Exp
elabTy = elabty

-- TODO this function should do mpre length checking
elabCastPats :: (Fresh m, MonadError C.Err m, WithDynDefs m, WithSourceLoc m) 
  => [Pat] -> Tel C.Term C.Ty C.Ty -> Ctx -> VMap 
  -> m ([(C.Pat, C.Exp)], C.Ty, [(C.Exp,C.Exp,C.Path)], Ctx, VMap)
elabCastPats [] (NoBnd outty) ctx rename = pure ([], outty, [], ctx, rename)
elabCastPats ((PVar x):rest) (TelBnd ty bndRestTel) ctx rename = do
  x' <- fresh $ s2n $ name2String x
  
  let exp = C.V x' $ ann ty
  let pat = C.PVar x'
  
  -- logg $ " ctx = " ++ lfullshow ctx
  (cpesexps, outty, eqs, ctx', rename') <- elabCastPats rest (substBind bndRestTel exp) (Map.insert x ty ctx) (Map.insert x x' rename)
  -- logg $ " ctx' = " ++ lfullshow ctx'
  pure ((pat,exp):cpesexps, outty, eqs, ctx', rename')

elabCastPats ((Pat dCName args):rest) (TelBnd topTy bndRestTel) ctx rename = do
  -- logg $ "topTy = " ++ show topTy
  (tCName, tel) <- getConsTcon dCName
  let telTy = unsafeTelMap (\ args -> C.TConF tCName args (ann $ NoBnd ())) tel
  (unzip -> (pats, exps), botTy, eqs, ctx', rename') <- elabCastPats args telTy ctx rename
  -- logg $ "botTy = " ++ show botTy

  -- let botTy = substsTel telTy exps 
  let botexp = C.DConF dCName exps $ ann (tCName, NoBnd $ snd $ substBindTel tel exps)
  -- logg $ "botexp = " ++ show botexp

  path <- fresh $ s2n "path"
  
  let exp = C.Csym botexp (C.PathV path $ ann (botTy, topTy)) (bind (s2n "x") $ C.V (s2n "x") $ ann C.TyU) $ ann topTy  -- TODO: this could be more specific becuase tcname is known
  
  -- logg $ "exp = " ++ show exp

  let pat = C.Pat path dCName pats
  -- logg $ "pat = " ++ show pat

  -- logg $ "... "
  let eq = (botTy, topTy, C.PathV path noAn) -- $ ann (botTy, topTy)) -- TODO: WHY CAN"T THE TYPE GO HERE?
  -- logg $ "eq = " ++ show eq

  (cpesexps, outty, eqs', ctx'', rename'') <- elabCastPats rest (substBind bndRestTel exp) ctx' rename'
  pure ((pat,exp):cpesexps, outty, eq : eqs ++ eqs', ctx'', rename'')
  
elabCastPats arg tel ctx rename = error $  " applications do not match type, " ++ show tel ++ "~/~" ++ show arg

--fill in the unwritten types with the types infered from scrutinee terms
-- TODO: a bit of a mess!
checkTelMaybe :: 
  (Fresh m, MonadError C.Err m, WithDynDefs m, WithSourceLoc m) 
  => [Term] -> Tel Exp (Maybe Ty) Ty
    -> Map C.Var C.Term
    -> Ctx -> VMap -> TyDefs 
             -> m ([C.Exp], C.Ty, (Tel C.Term C.Ty C.Ty))
checkTelMaybe [] (NoBnd a) defs ctx rename assumeDefs = do
  a' <- elabTy a ctx rename assumeDefs
  pure ([], substs (Map.toList defs) a', NoBnd a')
checkTelMaybe (trm : trms) (TelBnd (Just ty) bndRestTel) defs ctx rename assumeDefs = do
  cty <- elabTy ty ctx rename assumeDefs
  let ctyconcrete = substs (Map.toList defs) cty

  cexp <- elabCast trm ctyconcrete ctx rename assumeDefs
  -- logg "cexp"
  -- logg $ lfullshow cexp

  (x,restTel) <- unbind bndRestTel

  x' <- fresh $ s2n $ name2String x

  (args, a, telSym) <- checkTelMaybe trms restTel
    (Map.insert x' cexp defs) (Map.insert x cty ctx) (Map.insert x x' rename) assumeDefs
  
  pure (cexp : args, a, TelBnd cty $ bind x' telSym)

  
checkTelMaybe (trm : trms) (TelBnd Nothing bndRestTel) defs ctx rename assumeDefs = do
  cexp <- elabInf trm ctx rename assumeDefs
  let Just cty = C.tyInf cexp

  (x,restTel) <- unbind bndRestTel

  x' <- fresh $ s2n $ name2String x
  
  (args, a, telSym) <- checkTelMaybe trms restTel
    (Map.insert x' cexp defs) (Map.insert x cty ctx) (Map.insert x x' rename) assumeDefs
  
  pure (cexp : args, a, TelBnd cty $ bind x' telSym)
checkTelMaybe tel app _ _ _ _ = error $  " applications do not match type, " ++ show tel ++ "~/~" ++ show app




-- TODO depricate, infavor of something more general
elabCastTelUnit :: (Fresh m, MonadError C.Err m, WithDynDefs m, WithSourceLoc m) 
             => [Exp] -> Tel C.Term C.Ty ()
             -> Ctx -> VMap -> TyDefs 
             -> m [C.Exp]
elabCastTelUnit [] (NoBnd ()) ctx rename assumeDefs = pure []
elabCastTelUnit (trm : restTrm) (TelBnd ty bndRestTel) ctx rename assumeDefs = do
  cexp <- elabCast trm ty ctx rename assumeDefs
  -- logg "cexp"
  -- logg $ lfullshow cexp
  let restTel = substBind bndRestTel cexp
  -- logg "restTel"
  -- logg $ lfullshow restTel
  rest <- elabCastTelUnit restTrm restTel ctx rename assumeDefs
  pure $ cexp : rest
elabCastTelUnit _ _ _ _ assumeDefs = throwPrettyError " telescope different length"


unpacktel :: (Subst C.Ty a, Alpha a, Fresh m, MonadError C.Err m) => Tel C.Term C.Ty a -> [Var]
             -> (a -> Ctx -> VMap -> m b)
             -> Ctx -> VMap
             -> m b
unpacktel (NoBnd a) [] f ctx rename = f a ctx rename
unpacktel (TelBnd ty bndRestTel) (x : xs) f ctx rename = do
  x' <- fresh $ s2n $ name2String x
  unpacktel (substBind bndRestTel (C.V x' $ ann ty)) xs f (Map.insert x ty ctx) (Map.insert x x' rename)
unpacktel tel ls _ _ _ = error $ "applications do not match type" ++ show tel ++ " " ++ show ls

