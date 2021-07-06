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




module Dynamic.ElabModule where
import Prelude hiding (head, rem)

import Ast
import qualified Env as E
import qualified StdLib  as E
import qualified Dynamic.Ast as C
import qualified Dynamic.Err as C
import qualified Dynamic.Norm as C
import qualified Dynamic.Env as C
import Dynamic.Env
import Dynamic.Elab


import Data.Map (Map)
import qualified Data.Map as Map

import Data.Set (Set)
import qualified Data.Set as Set

import Unbound.Generics.LocallyNameless
import Control.Monad.Except
import Unbound.Generics.LocallyNameless.Unsafe (unsafeUnbind)

import UnboundHelper
import Control.Monad.Reader (runReader, ReaderT(runReaderT),  MonadReader(ask))
import Control.Monad.State
import Control.Monad.Identity

-- Elab the full module, a little hacky TODO: should only rely on the module typeclasses not the specific data




instance (Fresh m, MonadError C.Err m, Monad m, WithSourceLoc m) => (C.WithDynDefs (ElabMT m)) where
  getDatadef' tcName = ElabMT $ do
    (E.TyEnv _ dt _) <- ask
    case Map.lookup tcName dt of
      Nothing -> pure Nothing
      Just (DataDef _ cons) -> do
       tel <- unElabMT $ getTConnTel tcName
       consls <- forM (Map.toList cons) $ \ (dCName, _) -> do
         (_ , contel) <- unElabMT $ getConsTcon dCName
         pure (dCName, contel)
       pure $ Just $ C.DataDef tel $ Map.fromList consls 
 --  getDatadef

  getTConnTel tConn = ElabMT $ do
    (pc, _, _, _, _) <- get 
    case Map.lookup tConn pc of
      Just xx -> pure xx
      Nothing -> do
        (E.TyEnv _ dt _)  <- ask
        case Map.lookup tConn dt of
          Nothing -> throwPrettyError $ "could not find def of type constructor '" ++ tConn ++ "'"
          Just (DataDef tel _) -> do
            tel' <- unElabMT $ elabTelUnit tel Map.empty Map.empty 
            modify (\ (ptc, pdc, vmap, deftys, pdef) -> (Map.insert tConn tel' ptc, pdc, vmap, deftys, pdef) )
            pure tel'

  getConsTcon' dCName = ElabMT $ do
    (E.TyEnv _ dt _) <- ask
    case filter (\ (tCname, DataDef _ dd) -> Map.member dCName dd) $ Map.toList dt of
      [(tCname, DataDef _ dcons)] -> do
        telTys <- unElabMT $ getTConnTel tCname -- make sure the tc is resolved
        (_, pdc, _, _, _) <- get
        case Map.lookup tCname pdc >>= Map.lookup dCName of
         Just xx -> pure $ Just (tCname, xx)
         Nothing -> do
           let (Just tel) = Map.lookup dCName dcons
           tel' <- unElabMT $ elabTelLs tel telTys Map.empty Map.empty 
           modify (\ (ptc, pdc, vmap, deftys, pdef) -> (ptc, instertsert tCname dCName tel' pdc, vmap, deftys, pdef) )
           pure $ Just (tCname, tel')
      _ -> pure Nothing


  getDefnTy' x = ElabMT $ do
    x' <- elabdfnVar x
    (_, _, _, dfnty, _) <- get 
    case Map.lookup x' dfnty of
      Just ty -> pure $ Just (x',ty)
      Nothing -> do
        (E.TyEnv _ _ defn) <- ask
        case Map.lookup x defn of
          Nothing -> pure Nothing  
          Just (_,ty) -> do
            ty' <- unElabMT $ elabTy ty Map.empty Map.empty
            modify $ \ (ptc, pdc, vmap, defTy, pdef) ->  (ptc, pdc, vmap, Map.insert x' ty' defTy, pdef) 
            pure $ Just (x', ty')

  getDefn' x = ElabMT $ do
    mxty <- unElabMT $ getDefnTy' x
    case mxty of
      Nothing -> pure Nothing 
      Just (x', ty) -> do
        (_, _, _, _, dfn) <- get
        case Map.lookup x' dfn of
          Just trm -> pure $ Just (x',trm)
          Nothing -> do
            (E.TyEnv _ _ defn) <- ask
            let Just (trm,_) = Map.lookup x defn
            def <- unElabMT $ elabCast trm ty Map.empty Map.empty
            modify $ \ (ptc, pdc, vmap, defTy, pdef) ->  (ptc, pdc, vmap, defTy, Map.insert x' def pdef)
            pure $ Just (x', def)

  getDefnm' x = ElabMT $ do
    (_, _, _, _, dfn) <- get
    pure $ Map.lookup x dfn



elabTelUnit ::  (Fresh m, MonadError C.Err m, C.WithDynDefs m, WithSourceLoc m) => Tel Term Ty () -> Ctx -> VMap -> m (Tel C.Term C.Ty ())
elabTelUnit (NoBnd ()) _ _ = pure $ NoBnd ()
elabTelUnit (TelBnd ty bndbod) ctx rename = do
  ty' <- elabTy ty ctx rename
  (x, bod) <- unbind bndbod
  x' <- fresh $ s2n $ name2String x
  bod' <- elabTelUnit bod (Map.insert x ty' ctx) (Map.insert x x' rename)
  pure $ TelBnd ty' $ bind x' bod'

-- elabTelLs :: (Fresh m, MonadError C.Err m, MonadWithDynDefs m) => Tel Term Ty [Exp] -> Tel C.Term C.Ty () -> Ctx -> VMap -> m (Tel C.Term C.Ty [C.CastExp])
elabTelLs (NoBnd params) telltys ctx rename = do
  params' <- elabCastTelUnit params telltys ctx rename
  pure $ NoBnd params'
elabTelLs (TelBnd ty bndbod) telltys ctx rename = do
  ty' <- elabTy ty ctx rename 
  (x, bod) <- unbind bndbod
  x' <- fresh $ s2n $ name2String x
  bod' <- elabTelLs bod telltys (Map.insert x ty' ctx) (Map.insert x x' rename)
  pure $ TelBnd ty' $ bind x' bod'


elabdfnVar :: (Fresh m, MonadError C.Err m, MonadState Partialmodule m, MonadReader E.TyEnv m) => Var -> m C.Var
elabdfnVar x = do
  src@(E.TyEnv _ _ defn) <- ask
  (_, _, rename, _, _) <- get
  case Map.lookup x rename of
    Just x' -> pure x'
    Nothing -> do
      x' <- fresh $ s2n $ name2String x
      modify (\ (ptc, pdc, vmap, deftys, pdef) -> (ptc, pdc, Map.insert x x' vmap, deftys, pdef))
      pure x'

-- | run in an empty module
rem' :: ElabMT (WithSourceLocMT (FreshMT (ExceptT e Identity))) a -> E.TyEnv -> Either e (a, Partialmodule)
rem' e env = runIdentity $ runExceptT $ runFreshMT $ runWithSourceLocMT' $ runElabMT e env emp


rem e env s = runIdentity $ runExceptT $ runFreshMT $ runWithSourceLocMT (runElabMT e env emp) s


emp = (Map.empty, Map.empty,Map.empty,Map.empty,Map.empty)


instertsert :: (Ord k1, Ord k2) => k1 -> k2 -> v -> Map k1 (Map k2 v) -> Map k1 (Map k2 v)
instertsert k1 k2 v m = 
  case Map.lookup k1 m of
    Nothing -> Map.insert k1 (Map.singleton k2 v) m
    Just mm -> Map.insert k1 (Map.insert k2 v mm) m

-- Elab the full module, a little hacky TODO: should only rely on the module typeclasses not the specific data
elabmodule' :: E.TyEnv -> Either
     C.Err ((Map TCName C.DataDef, Map C.Var C.Term), Partialmodule)
elabmodule' src = elabmodule src Nothing  


elabmodule src@(E.TyEnv _ dt dfns) = rem (do
  let dfnVars = fmap fst $ Map.toList dfns
  -- -- mapM_ (\ x -> elabdfnVar' x src) dfnVars

  let tCnames = fmap fst $ Map.toList dt
  mapM_ (\ x -> getTConnTel x) tCnames

  let dCnames = concat $ fmap (\ (_, (DataDef _ cons)) -> Map.keys cons  ) $ Map.toList  dt
  mapM_ (\ x -> getConsTcon' x) dCnames

  mapM_ (\ x -> getDefnTy' x ) dfnVars
  mapM_ (\ x -> getDefn' x ) dfnVars

  termdefns <- mapM (\ x -> getDefn x ) dfnVars

  datadefls <- mapM (\ x -> do def <- getDatadef x; pure (x,def) ) tCnames

  pure  (Map.fromList datadefls, Map.fromList termdefns)
    )  src




-- | run under a surface language module, without source info
rununder' :: ElabMT (WithSourceLocMT ( FreshMT (ExceptT C.Err Identity))) a -> E.TyEnv -> Either C.Err (a, Partialmodule)
rununder' e src@(E.TyEnv _ dt dfns) = rem' (do
  let dfnVars = fmap fst $ Map.toList dfns
  -- -- mapM_ (\ x -> elabdfnVar' x src) dfnVars

  let tCnames = fmap fst $ Map.toList dt
  mapM_ (\ x -> getTConnTel x) tCnames

  let dCnames = concat $ fmap (\ (_, (DataDef _ cons)) -> Map.keys cons  ) $ Map.toList  dt
  mapM_ (\ x -> getConsTcon' x) dCnames

  mapM_ (\ x -> getDefnTy' x ) dfnVars
  mapM_ (\ x -> getDefn' x ) dfnVars

  termdefns <- mapM (\ x -> getDefn x ) dfnVars

  datadefls <- mapM (\ x -> do def <- getDatadef x; pure (x,def) ) tCnames

  pure  (Map.fromList datadefls, Map.fromList termdefns)

  e
    )  src



-- an elaborated version of the stdlib
stdlib :: Module
stdlib = Module datas (DefCtx defs) rename
  where
    Right ((datas,defs) , (_, _, rename , _ , _))  = elabmodule' $ E.stdlib
