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
{-# LANGUAGE DoAndIfThenElse #-}


module Dynamic.Elab where

import Prelude hiding (head)
  
import GHC.Stack

import Data.Typeable (Typeable)
import GHC.Generics (Generic)


import Ast
import qualified Env as E
import qualified Dynamic.Ast as C
-- import qualified Dynamic.Norm as C
import qualified Dynamic.Err as C
-- import qualified Dynamic.Env as C --TODO clean
-- import qualified Dynamic.Env as C --TODO clean
import Dynamic.Env hiding (whnf)
-- import Dynamic.Unification
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
import Unbound.Generics.LocallyNameless.Bind (Bind(B))
import Dynamic.Ast (Exp(DConF))
import Ty (substsTel)
import Dynamic.ElabBase
import Dynamic.Unification
import PreludeHelper
import Dynamic.Patttern
import Data.Either (partitionEithers)
import Control.Monad (forM)

-- if the type contains supstitutes insert a cast and return the substituted result
elabInf :: HasCallStack => (Fresh m, MonadError C.Err m, WithDynDefs m, WithSourceLoc m) => Ast.Exp -> ElabInfo m -> m (C.Exp, C.Ty)
elabInf e ctx@(ElabInfo {Dynamic.ElabBase.assign=assign}) = do
  (e', ty) <- elabInf' e ctx
  let s = ((\ (v, (term, _, _)) -> (v, term)) <$> Map.toList assign)
  let ty' = substs s ty
  if ty `aeq` ty' -- TODO erasable? normalizable?
  then pure (e', ty)
  else do
    let s' = ((\ (v, (_, tyWhy, why)) -> (v, (C.Union (C.V v) tyWhy why))) <$> Map.toList assign)
    pure (C.C e' (substs s' ty), ty')

elabInf' :: HasCallStack => (Fresh m, MonadError C.Err m, WithDynDefs m, WithSourceLoc m) => Ast.Exp -> ElabInfo m -> m (C.Exp, C.Ty)
elabInf' (Pos s e s') ctx = localSources s s' $ elabInf' e ctx
elabInf' (V x) ctx@(getVar x-> Just(x', ty)) = pure (C.V x', ty)
elabInf' (V x) (ElabInfo{varMap=Map.keys -> vars}) = throwPrettyError $ "bound var " ++ show x ++ " not in " ++ show vars
elabInf' (trm ::: ty) ctx = do
  -- loggg ""
  -- loggg "elabInf' :::"
  ty' <- elabCast ty C.TyU ctx
  -- loggg $ "ty' = " ++ lfullshow ty'
  tm' <- elabCast trm ty' ctx
  pure $ (tm', ty')
elabInf' TyU ctx = pure (C.TyU, C.TyU)
  
elabInf' (Pi aTy bndBod) ctx = do
  aTy' <- elabCast aTy C.TyU ctx
  (aName, bod) <- unbind bndBod
  (aName', ctx') <- setVar aName aTy' ctx
  bod' <- elabCast bod C.TyU ctx'
  pure $ (C.Pi aTy' $ bind aName' bod', C.TyU)

elabInf' (f `App` a) (ctx@ElabInfo{whnf=whnf}) = do
  -- loggg ""
  -- loggg "elabInf' App"
  (f', ty) <- elabInf f  ctx
  ty' <-  whnf ty
  -- loggg $ "ty' = "
  -- loggg $ lfullshow ty'

  case ty' of
    (C.Pi aTy bndBodTy) -> do
      -- -- loggg $ "aTy = " ++ lfullshow aTy
      a' <- elabCast a aTy ctx
      (aName, bodTybod) <- unbind bndBodTy
      pure $ (f' `C.App` a', substBind bndBodTy a')
    _ -> throwPrettyError $ "cannot apply a non-func " ++ show f ++ "  :  " ++ show ty' 

elabInf' (TCon tCname) ctx = do
  tel <- getTConnTel tCname
  pure $ (C.TConF tCname [] tel tel, toPi $ unsafeTelMap (\_ -> C.TyU) tel)

elabInf' (DCon dCname) ctx = do
  (tcName, tel) <- getConsTcon dCname
  ttel <- getTConnTel tcName
  pure $ (C.DConF dCname [] (tcName,tel) (unsafeTelMap (\_ -> ()) tel) ttel, 
    toPi $ unsafeTelMap (\inds -> C.TConF tcName inds (NoBnd ()) ttel) tel)

elabInf' (Case scrutinees (An (Just tel)) branches) ctx = do -- TODO extract this out of here and in the check into a function
  -- loggg ""
  -- loggg "elabInf' Case _"
  
  -- loggg "tel="
  loggg $ lfullshow tel
  (scrutinees', tel', caseTy) <- checkTelMaybe scrutinees tel ctx Map.empty
  
  -- loggg "tel'="
  -- loggg $ lfullshow tel'
  
  -- loggg "scrutinees'="
  -- loggg $ lfullshow scrutinees'
  -- loggg "caseTy="
  -- loggg $ lfullshow caseTy

  branches' <- forM branches $ \ (Match bndbod) -> do
    (pats, bod) <- unbind bndbod
    (pat, outTy, flexs, paths, eq, ctx') <- getPats pats tel' ctx
    logg "TODO needs to set up the equations with the already existing assignments"

    -- loggg $ "eq = " ++ lfullshow eq
    -- -- loggg $ "ctx' = " ++ show ctx'
    -- loggg $ "flexs = " ++ show flexs

    -- logg $ "fOUni flexs eq ctx'"
    uni <- fOUni flexs eq ctx'
    case uni of
      (Prob{unsat=e:_}) -> throwPrettyError $ "unsatisfieable pattern " ++ show e
      (Prob{active=[],stuck=[],Dynamic.Unification.assign= assign'}) -> do
        -- logg $ "worked!"
        -- loggg $ "assign' ="
        -- logg $ assign'
        -- loggg $ "outTy ="
        -- logg $ outTy
        bod' <- elabCast' bod outTy $ ctx'{Dynamic.ElabBase.assign= assign' `Map.union` Dynamic.ElabBase.assign ctx'}
        pure $ C.Match $ bind pat bod'
        
      (Prob{flex=flex,active=active',stuck=stuck'})  -> do
        -- loggg $ "uni=" ++ lfullshow uni
        -- loggg $ "active'=" ++ lfullshow active'
        -- loggg $ "stuck'=" ++ lfullshow stuck'
        -- loggg $ "flex=" ++ lfullshow flex
        throwPrettyError $ "unification timed out"
  
  pats' <- forM branches' $ \ (C.Match bndbod) -> do
    (pats, _) <- unbind bndbod
    pure pats

  vars <- fillFresh tel'
  unseenPats <- subAll [vars] pats'
  (partitionEithers -> (unmatched, silentCases)) <- forM unseenPats $ \ pats -> do
    (_, flexs, _, eq, ctx') <- getCPats pats tel' ctx
    logg "TODO needs to set up the equations with the already existing assignments"
    
    uni <- fOUni flexs eq ctx'
    -- should probly package up the unification with the unfufilled patterns
    case uni of
      (Prob{unsat=e@Equation{why=why,sameTy=sameTy}:_}) -> do
        
        logg "impossible case directed to blame"
        loggg $ lfullshow e
        logg ""
        pure $ Right $ C.Match $ bind pats $ C.Blame why sameTy
      _ -> pure $ Left pats

  sr <- askSourceRange

  pure (C.Case scrutinees' (branches'++silentCases) $ ann (unmatched, sr), caseTy)

elabInf' (Ref refName) _ = do
  ty <- getDefnTy refName
  pure (C.Ref refName, ty)

elabInf' e _ = throwPrettyError $ "cannot elab-infer " ++ show e


elabCast' :: HasCallStack => (Fresh m, MonadError C.Err m, WithDynDefs m, WithSourceLoc m) => Ast.Exp -> C.Ty -> ElabInfo m -> m C.Exp
elabCast' e ty ctx@(ElabInfo{Dynamic.ElabBase.assign=assign}) = do
  let s = ((\ (v, (term, _, _)) -> (v, term)) <$> Map.toList assign)
  let ty' = substs s ty
  if ty `aeq` ty' -- TODO erasable? normalizable?
  then elabCast e ty ctx
  else do
    let s' = ((\ (v, (_, tyWhy, why)) -> (v, (C.Union (C.V v) tyWhy why))) <$> Map.toList assign)
    e' <- elabCast e ty' ctx
    pure $ C.C e' (substs s' ty)


  -- (e', ty) <- elabInf' e ctx
  -- let s = ((\ (v, (term, _, _)) -> (v, term)) <$> Map.toList assign)


elabCast :: HasCallStack => (Fresh m, MonadError C.Err m, WithDynDefs m, WithSourceLoc m) => Ast.Exp -> C.Ty -> ElabInfo m -> m C.Exp
-- elabCast (Pos s e s') ty ctx = elabCast e ty ctx
elabCast (Pos s e s') ty ctx = localSources s s' $ elabCast e ty ctx
elabCast (Fun bbndBod) ty (ctx@ElabInfo{whnf=whnf}) = do
  -- loggg $ ""
  -- loggg $ "elabCast Fun _"
  -- loggg $ "ctx = " ++ show ctx
  -- loggg $ "ty = " ++ show ty
  -- loggg $ "ty = " ++ lfullshow ty
  -- loggg $ "bbndBod = " ++ lfullshow bbndBod
  ty' <-  whnf ty
  case ty' of
    (C.Pi aTy bndBodTy) -> do
      -- logg aTy' 
      ((selfName, aName), bod) <- unbind bbndBod
      (aName', ctx') <- setVar aName aTy ctx
      (selfName', ctx'') <- setVar selfName ty' ctx'
      -- logg $ "outTy = " ++ show outTy
      --   logg (C.TyUU aTy' $ C.V aName')

      bod' <- elabCast bod (substBind bndBodTy (C.V aName')) ctx''
      -- logg bod'

      pure $ C.Fun (bind (selfName', aName') bod') 
    e -> throwPrettyError $ "cast non pi to func " ++ show e ++ "  :  " ++ show ty' -- what if there is some wiggle room? not enough to safely infer a dependent output.
-- TODO several other syntaxes
-- elabCast (Case scrutinee (An Nothing) branches) ty ctx rename assumeDefs = throwPrettyError "not yet supporting case elaboration inference"


elabCast (Case scrutinees (An Nothing) branches) ty ctx = do  -- TODO extract this out of here and in the check into a function
  -- (ex', _)<- elabInf (Case scrutinees (ann $ dummyTellMaybe (length scrutinees) ty) branches) ctx  -- unfotunately can't just do this since ty has the wrong type
-- (Case scrutinees (An (Just tel)) branches) ctx 
  -- let tel = dummyTellMaybe (length scrutinees) ty
  -- loggg ""
  -- loggg "elabInf' Case _"
  
  (scrutinees', tel', caseTy) <- checkDummyTelMaybe scrutinees ty ctx Map.empty
  
  -- loggg "tel'="
  -- loggg $ lfullshow tel'
  
  -- loggg "scrutinees'="
  -- loggg $ lfullshow scrutinees'
  -- loggg "caseTy="
  -- loggg $ lfullshow caseTy

  branches' <- forM branches $ \ (Match bndbod) -> do
    (pats, bod) <- unbind bndbod
    (pat, outTy, flexs, paths, eq, ctx') <- getPats pats tel' ctx
    logg "TODO needs to set up the equations with the already existing assignments"

    -- loggg $ "eq = " ++ lfullshow eq
    -- -- loggg $ "ctx' = " ++ show ctx'
    -- loggg $ "flexs = " ++ show flexs

    -- logg $ "fOUni flexs eq ctx'"
    uni <- fOUni flexs eq ctx'
    case uni of
      (Prob{unsat=e:_}) -> throwPrettyError $ "unsatisfieable pattern " ++ show e
      (Prob{active=[],stuck=[],Dynamic.Unification.assign= assign'}) -> do
        -- logg $ "worked!"
        -- loggg $ "assign' ="
        -- logg $ assign'
        -- loggg $ "outTy ="
        -- logg $ outTy
        bod' <- elabCast' bod outTy $ ctx'{Dynamic.ElabBase.assign= assign' `Map.union` Dynamic.ElabBase.assign ctx'}
        pure $ C.Match $ bind pat bod'
        
      (Prob{flex=flex,active=active',stuck=stuck'})  -> do
        -- loggg $ "uni=" ++ lfullshow uni
        -- loggg $ "active'=" ++ lfullshow active'
        -- loggg $ "stuck'=" ++ lfullshow stuck'
        -- loggg $ "flex=" ++ lfullshow flex
        throwPrettyError $ "unification timed out"
  
  pats' <- forM branches' $ \ (C.Match bndbod) -> do
    (pats, _) <- unbind bndbod
    pure pats

  vars <- fillFresh tel'
  unseenPats <- subAll [vars] pats'
  (partitionEithers -> (unmatched, silentCases)) <- forM unseenPats $ \ pats -> do
    (_, flexs, _, eq, ctx') <- getCPats pats tel' ctx
    logg "TODO needs to set up the equations with the already existing assignments"
    
    uni <- fOUni flexs eq ctx'
    -- should probly package up the unification with the unfufilled patterns
    case uni of
      (Prob{unsat=e@Equation{why=why,sameTy=sameTy}:_}) -> do
        
        logg "impossible case directed to blame"
        loggg $ lfullshow e
        logg ""
        pure $ Right $ C.Match $ bind pats $ C.Blame why sameTy
      _ -> pure $ Left pats

  sr <- askSourceRange

  pure (C.Case scrutinees' (branches'++silentCases) $ ann (unmatched, sr))

elabCast e t ctx = do
  sr <- askSourceRange
  (e', t') <- elabInf e ctx
  if t' `aeq` t -- plug something more fancy here
  then pure e'
  else do
    pure $ C.C e' $ C.Same t' (C.initInfo sr t' t) C.TyU t -- TODO would need to ensure t' and t are : TyU

getPat :: HasCallStack => (Fresh m, MonadError C.Err m, WithDynDefs m, WithSourceLoc m) => Pat -> C.Ty -> ElabInfo m -> m (C.Pat, 
  Set C.Var, -- flex vars
  Set C.Var, -- path vars
  [Equation], ElabInfo m)
getPat (PVar x) ty info@(ElabInfo {varMap=varMap,tyCtx=tyCtx}) = do 
  x' <- fresh $ rename x
  pure (C.PVar x', Set.fromList [x'], Set.empty, [], info {varMap=Map.insert x x' varMap,tyCtx=Map.insert x' ty tyCtx })
getPat (Pat dCName args) ty info = do 
  p <- fresh $ s2n "p_"
  (tcName, tel) <- getConsTcon dCName
  ttel <- getTConnTel tcName
  let tytell = unsafeTelMap (\inds -> C.TConF tcName inds (NoBnd ()) ttel) tel
  (args', tyunder, flex, path, eqs, info') <- getPats args tytell info
  pure (C.Pat dCName args' p, flex, Set.insert p path, Equation tyunder ty C.TyU (C.V p):eqs, info')
  -- (args', flex, path, info') <- getPats args info
  -- pure (C.Pat dCName args' p, flex, Set.insert p path, info')

--
  -- pure $ (C.DConF dCname [] (tcName,tel) (unsafeTelMap (\_ -> ()) tel) ttel, 
  --   toPi $ unsafeTelMap (\inds -> C.TConF tcName inds (NoBnd ()) ttel) tel)

getPats :: HasCallStack => (Fresh m, MonadError C.Err m, WithDynDefs m, WithSourceLoc m) => [Pat] -> Tel C.Term C.Ty C.Ty -> ElabInfo m -> m ([C.Pat], C.Ty, Set C.Var, Set C.Var, [Equation], ElabInfo m)
getPats [] (NoBnd ty) info = pure ([],ty, Set.empty,Set.empty,[],info)
getPats (arg:rest) (TelBnd argTy bndTelRest) info = do
  (arg', flex, path, eqs, info') <- getPat arg argTy info
  earg'<- patAsExp arg'
  (args', ty, flex', path',eqs', info'') <- getPats rest (substBind  bndTelRest earg')info'
  pure (arg':args', ty, flex `Set.union` flex',path `Set.union` path', eqs ++ eqs', info'')
getPats _ _ _ = error $ " applications do not match type (TODO better error)" 


getCPat (C.PVar x) ty info@(ElabInfo {tyCtx=tyCtx}) = do 
  pure (Set.fromList [x], Set.empty, [], info {tyCtx=Map.insert x ty tyCtx })
getCPat (C.Pat dCName args p) ty info = do 
  (tcName, tel) <- getConsTcon dCName
  ttel <- getTConnTel tcName
  let tytell = unsafeTelMap (\inds -> C.TConF tcName inds (NoBnd ()) ttel) tel
  (tyunder, flex, path, eqs, info') <- getCPats args tytell info
  pure (flex, Set.insert p path, Equation tyunder ty C.TyU (C.V p):eqs, info')

getCPats :: HasCallStack => (Fresh m, MonadError C.Err m, WithDynDefs m, WithSourceLoc m) => [C.Pat] -> Tel C.Term C.Ty C.Ty -> ElabInfo m -> m (C.Ty, Set C.Var, Set C.Var, [Equation], ElabInfo m)
getCPats [] (NoBnd ty) info = pure (ty, Set.empty,Set.empty,[],info)
getCPats (arg:rest) (TelBnd argTy bndTelRest) info = do
  (flex, path, eqs, info') <- getCPat arg argTy info
  earg'<- patAsExp arg
  (ty, flex', path',eqs', info'') <- getCPats rest (substBind  bndTelRest earg') info'
  pure (ty, flex `Set.union` flex', path `Set.union` path', eqs ++ eqs', info'')
getCPats _ _ _ = error $ " applications do not match type (TODO better error)" 

patAsExp :: (Fresh m, MonadError C.Err m, WithDynDefs m, WithSourceLoc m) => C.Pat -> m C.Exp 
patAsExp (C.PVar x) = pure $ C.V x
patAsExp (C.Pat dcName args p) = do
  args' <- forM args patAsExp
  (tcName, tel) <- getConsTcon dcName
  ttel <- getTConnTel tcName
  pure $ C.C (C.DConF dcName args' (tcName, NoBnd $ substsTel tel args') (unsafeTelMap (\inds -> ()) tel) ttel) $ C.V p



toPi :: Tel C.Term C.Ty C.Exp -> C.Exp
toPi (NoBnd e) = e
toPi (TelBnd aTy (B p bod)) = C.Pi aTy (B p $ toPi bod)
-- unsafeTelMap f (NoBnd b) = NoBnd $ f b
-- unsafeTelMap f (TelBnd a (B p bod)) = TelBnd a (B p $ unsafeTelMap f bod)

--fill in the unwritten types with the types infered from scrutinee terms
-- TODO: a bit of a mess!
checkTelMaybe :: 
  (Fresh m, MonadError C.Err m, WithDynDefs m, WithSourceLoc m) 
  => [Term] -> Tel Ast.Exp (Maybe Ty) Ty
  -> ElabInfo m
  -> Map C.Var C.Term 
  -> m ([C.Exp], -- elaborated scrutinees
   (Tel C.Term C.Ty C.Ty), -- elaborated telescope
    C.Ty -- result of the telescope with scrutinees applied
   )
checkTelMaybe [] (NoBnd a) ctx defs = do
  a' <- elabCast a C.TyU ctx
  pure ([], NoBnd a', substs (Map.toList defs) a')
checkTelMaybe (trm : trms) (TelBnd (Just ty) bndRestTel) ctx defs = do
  cty <- elabCast ty C.TyU ctx
  let ctyconcrete = substs (Map.toList defs) cty
  -- loggg ""
  -- loggg "checkTelMaybe"
  -- loggg $ "ctyconcrete ="
  -- logg ctyconcrete
  cexp <- elabCast trm ctyconcrete ctx
  -- loggg "cexp ="
  -- logg cexp

  (x,restTel) <- unbind bndRestTel
  (x', ctx') <- setVar x cty ctx

  (args, telSym, a) <- checkTelMaybe trms restTel ctx' (Map.insert x' cexp defs)
  
  pure (cexp : args, TelBnd cty $ bind x' telSym, a)

checkTelMaybe (trm : trms) (TelBnd Nothing bndRestTel) ctx defs  = do
  (cexp, cty) <- elabInf trm ctx

  (x,restTel) <- unbind bndRestTel
  (x', ctx') <- setVar x cty ctx

  (args, telSym, a) <- checkTelMaybe trms restTel ctx' (Map.insert x' cexp defs)
  
  pure (cexp : args, TelBnd cty $ bind x' telSym, a)
checkTelMaybe app tel _ _ = error $  " scrutinees do not match tell, " ++ show app ++ "~/~" ++ show tel


checkDummyTelMaybe :: 
  (Fresh m, MonadError C.Err m, WithDynDefs m, WithSourceLoc m) 
  => [Term] -> C.Ty
  -> ElabInfo m
  -> Map C.Var C.Term 
  -> m ([C.Exp], -- elaborated scrutinees
   (Tel C.Term C.Ty C.Ty), -- elaborated telescope
    C.Ty -- result of the telescope with scrutinees applied
   )
-- checkDummyTelMaybe = undefined
checkDummyTelMaybe [] a' ctx defs = do
  -- a' <- elabCast a C.TyU ctx
  pure ([], NoBnd a', substs (Map.toList defs) a')

checkDummyTelMaybe (trm : trms) a' ctx defs  = do
  (cexp, cty) <- elabInf trm ctx

  x <- fresh $ s2n "p"
  (x', ctx') <- setVar x cty ctx

  (args, telSym, a) <- checkDummyTelMaybe trms a' ctx' (Map.insert x' cexp defs)
  
  pure (cexp : args, TelBnd cty $ bind x' telSym, a)
-- checkTelMaybe app tel _ _ = error $  " scrutinees do not match tell, " ++ show app ++ "~/~" ++ show tel




-- TODO depricate, infavor of something more general
elabCastTelUnit :: (Fresh m, MonadError C.Err m, WithDynDefs m, WithSourceLoc m) 
             => [Ast.Exp] -> Tel C.Term C.Ty ()
             -> (ElabInfo m)
             -> m [C.Exp]
elabCastTelUnit [] (NoBnd ()) ctx = pure []
elabCastTelUnit (trm : restTrm) (TelBnd ty bndRestTel) ctx = do
  
  -- loggg ""
  -- loggg "elabCastTelUnit"
  -- loggg $ "ty " ++ lfullshow ty
  cexp <- elabCast trm ty ctx
  -- -- logg "cexp"
  -- -- logg $ lfullshow cexp
  let restTel = substBind bndRestTel cexp
  -- -- logg "restTel"
  -- -- logg $ lfullshow restTel
  rest <- elabCastTelUnit restTrm restTel ctx
  pure $ cexp : rest
elabCastTelUnit _ _ _  = throwPrettyError " telescope different length"


-- unpacktel :: (Subst C.Ty a, Alpha a, Fresh m, MonadError C.Err m) => Tel C.Term C.Ty a -> [Var]
--              -> (a -> Ctx -> VMap -> m b)
--              -> Ctx -> VMap
--              -> m b
-- unpacktel (NoBnd a) [] f ctx rename = f a ctx rename
-- unpacktel (TelBnd ty bndRestTel) (x : xs) f ctx rename = do
--   x' <- fresh $ s2n $ name2String x
--   unpacktel (substBind bndRestTel (C.V x' $ ann ty)) xs f (Map.insert x ty ctx) (Map.insert x x' rename)
-- unpacktel tel ls _ _ _ = error $ "applications do not match type" ++ show tel ++ " " ++ show ls

