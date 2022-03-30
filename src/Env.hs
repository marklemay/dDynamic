{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ViewPatterns #-}

module Env where

import GHC.Stack

import Unbound.Generics.LocallyNameless
import GHC.Generics (Generic)
import Data.Typeable (Typeable)

import Data.Map (Map)
import qualified Data.Map as Map

import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad.Identity

import UnboundHelper

import Control.Applicative

import Ast

import PreludeHelper

import SourcePos

type TyCtx = Map Var Ty
type DataCtx = Map TCName DataDef

-- TODO: work better with source pos

-- For toplevel term definitions
type DefCtx = Map RefName (Term, Ty)

type Module = (Map TCName DataDef, DefCtx)

-- TODO clean up the notion of module, undermodule

-- | rempaps all the unbound vars that match dataconstructors and typeconstructors 
undermodule :: (Subst Exp a) => a -> DataCtx -> Map RefName (Term, Ty) -> a
undermodule e datals (Map.keys-> refs)  = underData (underRef e refs) datals 


underRef :: (Subst Exp a) => a -> [RefName] -> a
underRef e (refls)  = substs (fmap (\ r -> (s2n r, Ref r)) refls) e


underData :: (Subst Exp a) => a -> DataCtx -> a
underData e (Map.toList-> datals) = undermodule' e datals

undermodule' :: (Subst Exp a) => a -> [(TCName, DataDef)] -> a
undermodule' e [] = e
-- undermodule' e ((tCname, DataDef (NoBnd ()) (Map.toList-> ls)) : rest) = 
--   subst (s2n tCname) (TCon tCname []) $ underConstructors' (undermodule' e rest) (fst <$> ls) 
undermodule' e ((tCname, DataDef _ (Map.toList-> ls)) : rest) = 
  subst (s2n tCname) (TCon tCname) $ underConstructors' (undermodule' e rest) (fst <$> ls) 

underConstructors' :: (Subst Exp a) => a -> [DCName] -> a
underConstructors' e [] = e
underConstructors' e (dCname : rest) = subst (s2n dCname) (DCon dCname) $ underConstructors' e rest

-- TODO : can memoize solutions in the envrironment

data TyEnv = TyEnv {tyCtx :: TyCtx, dataCtx :: DataCtx, defCtx :: DefCtx}
  deriving (Show,Eq)

empTyEnv = TyEnv Map.empty Map.empty Map.empty 
--TODO: is there not a standard way to add constaints to the reader ctx?



-- class VarCtx ctx where 
--    inCtx :: ctx -> Var -> Bool

class TypingCtx ctx where 
-- class (VarCtx ctx) => TypingCtx ctx where 
   getVarTy :: (MonadError String m) => ctx -> Var -> m Ty
  --  inCtx ctx var = undefined

instance TypingCtx TyCtx where
  getVarTy tyCtx v = 
    case Map.lookup v tyCtx of
      Just ty -> pure ty
      Nothing -> throwError $ "could not find " ++ show v ++ " in " ++ show tyCtx

-- instance TypingCtx DefCtx where
--   getVarTy defCtx v = 
--     case Map.lookup v defCtx of
--       Just (_,ty) -> pure ty
--       Nothing -> throwError $ "could not find " ++ show v ++ " in " ++ show defCtx

instance TypingCtx TyEnv where
  getVarTy (TyEnv{tyCtx=tyCtx}) v =
     getVarTy tyCtx v 

instance TypingCtx (TyEnv,a) where -- on the hacky side
  getVarTy (TyEnv{tyCtx=tyCtx},_) v =
     getVarTy tyCtx v


lookupTy :: (MonadReader ctx m, TypingCtx ctx, MonadError String m)
  => Var -> m Ty
lookupTy v = do
  ctx <- ask
  getVarTy ctx v


class DataingCtx ctx where 
   getDatadef :: (MonadError String m) => ctx -> TCName ->  m DataDef

   getConsTcon :: (MonadError String m) => ctx -> DCName ->  m (TCName, Telescope [Term])

instance DataingCtx DataCtx where
   getDatadef ctx tcname = 
    case Map.lookup tcname ctx of
      Just dat -> pure dat
      Nothing -> throwError $ "could not find " ++ show tcname ++ " in " ++ show ctx
   
   getConsTcon ctx dCName = case  do -- List monad
      (tCName, DataDef _ cons) <- Map.toList ctx
      tel <- justM $ Map.lookup dCName cons 
      pure (tCName, tel)
    of x : _ -> pure x
       _ -> throwError $ "data constructor '" ++ show dCName ++ "' not found in ctx"

instance DataingCtx TyEnv where
   getDatadef (TyEnv tyCtx dataCtx defCtx) = getDatadef dataCtx
   getConsTcon (TyEnv tyCtx dataCtx defCtx) = getConsTcon dataCtx



instance DataingCtx (TyEnv,a) where
   getDatadef (TyEnv tyCtx dataCtx defCtx, _) = getDatadef dataCtx
   getConsTcon (TyEnv tyCtx dataCtx defCtx, _) = getConsTcon dataCtx



lookupDataDef :: (MonadReader ctx m, DataingCtx ctx, MonadError String m) 
  => TCName -> m DataDef
lookupDataDef tCName = do
  ctx <- ask
  getDatadef ctx tCName 

lookupDCName :: (MonadReader ctx m, DataingCtx ctx, MonadError String m)
  => DCName -> m (TCName, Telescope [Term])
lookupDCName dCName = do
  ctx <- ask
  getConsTcon ctx dCName

lookupTCName :: (MonadReader ctx m, DataingCtx ctx, MonadError String m)
  => TCName -> m (Telescope ())
lookupTCName tCName = do
  DataDef termIndex  _ <- lookupDataDef tCName
  pure termIndex



class DefnCtx ctx where 
  getDefn' :: ctx -> RefName -> Maybe (Term, Ty)



instance DefnCtx DefCtx where 
   getDefn' defCtx v = Map.lookup v defCtx


instance DefnCtx TyEnv where 
   getDefn' (TyEnv tyCtx dataCtx defCtx) = getDefn' defCtx


instance DefnCtx (TyEnv,a) where 
   getDefn' (TyEnv tyCtx dataCtx defCtx,a) = getDefn' defCtx

-- TODO this should be the definition
-- lookupDef' :: (MonadReader ctx m, DefnCtx ctx) => Var -> m (Maybe (Term, Ty))
lookupDef' :: HasCallStack => (MonadReader ctx m, DefnCtx ctx) => RefName -> m (Maybe (Term, Ty))
lookupDef' v = do 
  ctx <- ask
  pure $ getDefn' ctx v


-- TODO make these types sigs more uniform
--lookupDef :: Var -> TcMonad (Maybe (Term, Ty))
lookupDef :: HasCallStack => (MonadReader ctx m, DefnCtx ctx, MonadError String m) => RefName -> m (Term, Ty)
lookupDef v = do
  ma <- lookupDef' v
  case ma of
    Just p -> pure p
    Nothing -> throwError $ "could not find deffinition '" ++ show v ++ "'" -- in " ++ show defCtx
  -- (TyEnv tys datas defCtx) <- ask
  -- pure $ Map.lookup v defCtx

-- TODO: add a writer to this for debug logging
-- most operations can use this monad
type TcMonad = FreshMT (ReaderT (TyEnv, Maybe SourceRange) (ExceptT String Identity))

empctx :: TyEnv
empctx = TyEnv Map.empty Map.empty  Map.empty

runTcMonad :: TyEnv -> TcMonad a -> Either String a
runTcMonad ctx m = runIdentity $ runExceptT $ runReaderT (runFreshMT m) (ctx, Nothing)

-- TODO should actually carry this information Entirely in sytax
runTcMonadS :: String -> String -> TyEnv -> TcMonad a -> Either String a
runTcMonadS path s ctx m = runIdentity $ runExceptT $ runReaderT (runFreshMT m) (ctx, Just (fullRange path s))


-- TODO: IO versions, for better error handling and reporting http://dev.stephendiehl.com/hask/#error-handling
runTcMonadIo :: HasCallStack => TyEnv -> TcMonad a -> IO a
runTcMonadIo ctx ma = do
  let res = runTcMonad ctx ma
  case res of
    Left s -> errIo s
    Right a -> pure a

-- runTcMonadSIo :: HasCallStack => String -> String -> TyEnv -> TcMonad a -> IO a
-- runTcMonadSIo path s ctx ma = do
--   let res = runTcMonadS path s ctx ma
--   case res of
--     Left s -> throwError $ userError s
--     Right a -> pure a




-- TODO: generalize the typeclasses here?
extendCtx :: Var -> Ty -> TcMonad a -> TcMonad a
extendCtx name typ = local $ \ (TyEnv tys datas dfnCtx, p) -> (TyEnv (Map.insert name typ tys) datas dfnCtx, p) --TODO: lenses :(

-- extendDef :: Var -> Term -> Ty -> TcMonad a -> TcMonad a
-- extendDef name term typ = local $ \ (TyEnv tys datas dfnCtx, p) -> (TyEnv tys datas (Map.insert name (term, typ) dfnCtx), p) --TODO: lenses :(

setRegion :: SourcePos -> SourcePos -> TcMonad a -> TcMonad a
setRegion l r = local $ \ (e, m) -> 
  case m of
    Just (SourceRange ms _ _) -> (e, Just (SourceRange ms l r))
    Nothing -> (e, Nothing)

-- getregion :: TcMonad (Maybe (String, SourcePos, SourcePos))
-- getregion = do
--   (_, mr) <- ask
--   pure mr

throwprettyError :: HasCallStack => String -> TcMonad a
throwprettyError msg = do
  (_,mreg)<- ask
  throwError $ msg ++
    case mreg of
      Nothing -> ""
      Just reg -> "\n" ++ (unlines $ prettyRange reg)
    ++ "\n" ++ prettyCallStack callStack

-- guardThrow :: HasCallStack => MonadError String m => Bool -> String -> m a -> m a
guardThrow True s ma = ma
guardThrow False s ma = throwError $ s ++ "\n" ++ prettyCallStack callStack

-- infoGuard :: HasCallStack => MonadError String m => String -> Bool -> m ()
infoGuard _ True  = pure ()
infoGuard s False = throwprettyError $ s ++ "\n" ++ prettyCallStack callStack

infJustM s (Just a) = pure a
infJustM s Nothing = throwprettyError $ s ++ "\n" ++ prettyCallStack callStack

-- justM :: HasCallStack => MonadError String m => String -> Bool -> m ()
-- justM 

-- setText :: String -> TcMonad a -> TcMonad a
-- setText s = local $ \ (e, _) -> (e, Just (s,SourcePos "" 0 0 , endPos "" s))



--TODO: would be nice to generalize over every pattern?

-- TODO: bit of a mess, TODO add unbind to the name?
-- TODO: observe usage, perhaps a better way to order params?
-- TODO: (Alpha a) => Bind Var a -> Ty -> ( a -> Var -> TcMonad  b) -> TcMonad (Var , b)
inCtxWith :: (Alpha a) => Bind Var a -> Ty -> ( a -> TcMonad  b) -> TcMonad (Var , b)
inCtxWith bnd typ rest = do (name, bod) <- unbind bnd; extendCtx name typ $ do ans <- rest bod ; pure $ (name, ans)


freshTy :: Var -> Ty -> ( Var -> TcMonad  b) -> TcMonad b
freshTy n typ rest = do
  name <- fresh n
  extendCtx name typ $ rest name


-- TODO: where should this live?
tellAsFun :: (Alpha t, Fresh m) => Telescope t -> (t -> m Ty) -> m Ty
tellAsFun (NoBnd a) f = f a
tellAsFun (TelBnd aTy bndRest) f = do
  (aName, rest) <- unbind bndRest
  bodTy <- tellAsFun rest f
  pure $ Pi aTy $ bind aName bodTy