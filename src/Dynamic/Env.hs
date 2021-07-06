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


module Dynamic.Env where

import GHC.Stack ( HasCallStack )

import Ast
import qualified Env as E
import qualified Dynamic.Ast as C
import qualified Dynamic.Err as C
import qualified Dynamic.Temp as C
import qualified Dynamic.Erase as C

import Data.Map (Map)
import qualified Data.Map as Map

import Data.Set (Set)
import qualified Data.Set as Set

import Unbound.Generics.LocallyNameless
import Control.Monad.Except
import Unbound.Generics.LocallyNameless.Unsafe (unsafeUnbind)

import UnboundHelper
import Control.Monad.Reader
import Control.Monad.State

import Control.Applicative

import SourcePos
import Dynamic.Err

-- machinery to translate module definitions from the surface language into the core languguage

type TyCtx = Map Var Ty
type DataCtx = Map TCName C.DataDef


type Partialmodule = (Map String (Tel C.Term C.Ty ()), Map String (Map String (Tel C.Term C.Ty [C.Ty])), VMap, Map C.Var C.Ty, Map C.Var C.Term)




data Module = Module DataCtx DefCtx VMap
  deriving Show

makeMod :: Map TCName C.DataDef -> Map C.Var C.Term -> Module
makeMod ddefs trmdefs = Module ddefs (DefCtx trmdefs) $ Map.fromList $ fmap (\(k, _) -> (s2n $ name2String k,k)) $ Map.toList trmdefs

-- | For toplevel term definitions
newtype DefCtx = DefCtx (Map C.Var C.Term)
  deriving Show

type VMap = Map Var C.Var


undermodule :: (Subst Exp a) => a -> Module -> a
undermodule e (Module (Map.toList-> ls) _ _) = undermodule' e ls

-- undermodule' :: (Subst Exp a) => a -> [(TCName, DataDef)] -> a
undermodule' e [] = e
-- undermodule' e ((tCname, DataDef (NoBnd ()) (Map.toList-> ls)) : rest) = 
--   subst (s2n tCname) (TCon tCname []) $ underConstructors' (undermodule' e rest) (fst <$> ls) 
undermodule' e ((tCname, C.DataDef _ (Map.toList-> ls)) : rest) = 
  subst (s2n tCname) (TCon tCname) $ underConstructors' (undermodule' e rest) (fst <$> ls) 

-- underConstructors' :: (Subst Exp a) => a -> [DCName] -> a
underConstructors' e [] = e
underConstructors' e (dCname : rest) = subst (s2n dCname) (DCon dCname) $ underConstructors' e rest






-- a interface to get partial module info out of the environment
class (Monad m) => WithDynDefs m where 
   getDatadef' :: TCName -> m (Maybe C.DataDef)
   getDatadef :: (WithSourceLoc m, MonadError C.Err m) => TCName -> m C.DataDef
   getDatadef tCName = do
     mdef <- getDatadef' tCName
     case mdef of 
       Nothing -> throwPrettyError $ "tCName not found " ++ tCName
       Just def -> pure def

   getTConnTel :: (WithSourceLoc m, MonadError C.Err m) => TCName -> m (Tel C.Term C.Ty ())
   getTConnTel tCName = do
     (C.DataDef tel _ ) <- getDatadef tCName
     pure tel

   getConsTcon' :: DCName -> m (Maybe (TCName, Tel C.Term C.Ty [C.Term]))
   getConsTcon :: (WithSourceLoc m, MonadError C.Err m) => DCName ->  m (TCName, Tel C.Term C.Ty [C.Term])
   getConsTcon dCName = do
     mdef <- getConsTcon' dCName
     case mdef of 
       Nothing -> throwPrettyError $ "dCName not found " ++ dCName
       Just def -> pure def
       

   getDefnTy' :: Var -> m (Maybe (C.Var,C.Term))

   getDefn' :: Var -> m (Maybe (C.Var, C.Term))
   getDefn :: (WithSourceLoc m, MonadError C.Err m) => Var -> m (C.Var, C.Term)
   getDefn x = do
     mx <- getDefn' x
     case mx of
       Just ans -> pure ans 
       Nothing ->  throwPrettyError $  "binding not found " ++ show x


   getDefnm' :: C.Var -> m (Maybe C.Term)
   -- TODO explicitly handle the var remapping?



instance (WithDynDefs m) => (WithDynDefs (FreshMT m)) where
  getDatadef' = lift . getDatadef' 
  getConsTcon' = lift . getConsTcon'
  getDefn' = lift . getDefn' 
  getDefnTy' = lift . getDefnTy'
  getDefnm' = lift . getDefnm'

instance (WithDynDefs m) => (WithDynDefs (ExceptT e m)) where
  getDatadef' = lift . getDatadef' 
  getConsTcon' = lift . getConsTcon'
  getDefn' = lift . getDefn'
  getDefnTy' = lift . getDefnTy'
  getDefnm' = lift . getDefnm'

newtype WithModuleMT m a = WithModuleMT {unWithModuleMT :: ReaderT Module m a}
  deriving
    ( Functor
    , Applicative
    , Alternative
    , Monad
    , MonadIO
    , MonadPlus
    , MonadFix
    )

runWithModuleMT :: WithModuleMT m a -> Module -> m a
runWithModuleMT e m = runReaderT (unWithModuleMT e) m


instance MonadTrans WithModuleMT where
  lift = WithModuleMT . lift


instance (Fresh m) => (Fresh (WithModuleMT m)) where
  fresh = lift . fresh

instance (MonadError e m) => (MonadError e (WithModuleMT m)) where
  throwError = lift . throwError
  catchError m h = error "not done yet"

instance (Fresh m, Monad m) => (WithDynDefs (WithModuleMT m)) where
  getDatadef' tcName = WithModuleMT $ do
    (Module dataCtx defCtx vMap) <- ask
    pure $ Map.lookup tcName dataCtx

  getConsTcon' dCName =  WithModuleMT $ do
    (Module dataCtx defCtx vMap) <- ask
    case filter (\ (tCname, C.DataDef _ dd) -> Map.member dCName dd) $ Map.toList dataCtx of
      [(tCname, C.DataDef _ dcons)] -> do
        let Just tel = Map.lookup dCName dcons
        pure $ Just (tCname, tel)
      _ -> pure Nothing 

  getDefn' x = WithModuleMT $ do
    (Module dataCtx (DefCtx defCtx) vMap) <- ask
    case Map.lookup x vMap of
      Nothing -> pure Nothing
      Just x' -> 
        case Map.lookup x' defCtx of
          Nothing -> pure Nothing 
          Just def -> pure $ Just (x', def)
  getDefnTy' x =  WithModuleMT $ do
    (Module dataCtx (DefCtx defCtx) vMap) <- ask
    case Map.lookup x vMap of
      Nothing -> pure Nothing
      Just x' -> 
        case Map.lookup x' defCtx of
          Nothing -> pure Nothing 
          Just def -> pure $ Just (x', C.apparentTy def)

  getDefnm' x  =  WithModuleMT $ do
    (Module dataCtx (DefCtx defCtx) vMap) <- ask
    pure $ Map.lookup x defCtx 

newtype ElabMT m a = ElabMT {unElabMT :: ReaderT E.TyEnv (StateT Partialmodule m) a}
  deriving
    ( Functor
    , Applicative
    , Alternative
    , Monad
    , MonadIO
    , MonadPlus
    , MonadFix
    )


runElabMT :: ElabMT m a -> E.TyEnv -> Partialmodule -> m (a, Partialmodule)
runElabMT e env s = runStateT (runReaderT (unElabMT e) env) s

instance MonadTrans ElabMT where
  lift = ElabMT . lift . lift


instance (Fresh m) => (Fresh (ElabMT m)) where
  fresh = lift . fresh

instance (MonadError e m) => (MonadError e (ElabMT m)) where
  throwError = lift . throwError
  catchError m h = error "not done yet"
--m h = FreshMT $ EC.catchError (unFreshMT m) (unFreshMT . h)


--TODO belongs somewhere else?
class (Monad m) => WithSourceLoc m where
  localSourceRange :: SourceRange -> m a -> m a
  -- TODO make this properly local?

  askSourceRange :: m (Maybe SourceRange)

localSourceRangeFrom :: WithSourceLoc m  => Exp -> m a -> m a
localSourceRangeFrom (Pos l e r) ma = do
  sr <- askSourceRange
  case sr of
    Just (SourceRange msrc _ _) -> localSourceRange (SourceRange msrc l r) $ localSourceRangeFrom e ma
    Nothing -> localSourceRange (SourceRange Nothing l r) $ localSourceRangeFrom e ma
localSourceRangeFrom _ ma = ma


localSources :: WithSourceLoc m  => SourcePos -> SourcePos -> m a -> m a
localSources l r ma = do
  sr <- askSourceRange
  case sr of
    Just (SourceRange msrc _ _) -> localSourceRange (SourceRange msrc l r) ma
    Nothing -> localSourceRange (SourceRange Nothing l r) ma

newtype WithSourceLocMT m a = WithSourceLocMT {unWithSourceLocMT :: ReaderT (Maybe SourceRange) m a}
  deriving
    ( Functor
    , Applicative
    , Alternative
    , Monad
    , MonadIO
    , MonadPlus
    , MonadFix
    )

runWithSourceLocMT' m = runReaderT (unWithSourceLocMT m) Nothing

runWithSourceLocMT m sr = runReaderT (unWithSourceLocMT m) sr


instance (Monad m) => (WithSourceLoc (WithSourceLocMT m)) where
  localSourceRange s ma = WithSourceLocMT $ local (\_ -> Just s) $ unWithSourceLocMT ma
  askSourceRange = WithSourceLocMT ask

instance MonadTrans WithSourceLocMT where
  lift = WithSourceLocMT . lift 


instance (WithSourceLoc m) => (WithSourceLoc (StateT s m)) where
  localSourceRange src ma = StateT $ \s -> localSourceRange src $ runStateT ma s
  askSourceRange = lift askSourceRange

  
instance (WithSourceLoc m) => (WithSourceLoc (ReaderT r m)) where
  localSourceRange src ma = ReaderT $ \ r -> localSourceRange src  $ runReaderT ma r
  askSourceRange = lift askSourceRange


instance (WithSourceLoc m) => (WithSourceLoc (ElabMT m)) where
  localSourceRange s ma = let
    ee e p = localSourceRange s $ runStateT (runReaderT (unElabMT ma) e) p
    in ElabMT $ ReaderT $ \ty ->  StateT $ ee ty -- TODO could be substantially prettier

  askSourceRange = lift askSourceRange

instance (Fresh m) => (Fresh (WithSourceLocMT m)) where
  fresh = lift . fresh

instance (MonadError e m) => (MonadError e (WithSourceLocMT m)) where
  throwError = lift . throwError
  catchError m h = error "not done yet"
--m h = FreshMT $ EC.catchError (unFreshMT m) (unFreshMT . h)

instance WithDynDefs m => WithDynDefs (WithSourceLocMT m) where
  getDatadef' = lift . getDatadef'
  getConsTcon' = lift . getConsTcon'
  getDefnTy' = lift . getDefnTy' 
  getDefn' = lift . getDefn'
  getDefnm' = lift . getDefnm'

throwPrettyError :: HasCallStack => (WithSourceLoc m, MonadError Err m) => String -> m b
throwPrettyError s = do
  sr <- askSourceRange
  throwError $ Msg s sr


throwInfoError :: HasCallStack => (MonadError Err m) => String -> C.Info -> m b
throwInfoError s (C.Info sr obs ctx l r) = do
  runWithSourceLocMT (throwPrettyError $ unlines $
    ["",
    show (C.e $ unignore l) ++ " =/= " ++  show (C.e $ unignore r)
    ] ++ (case prettyShowCtx ctx of
           [] -> []
           pctx -> "since when " : pctx  )
      ++ [case prettyobs obs of
           "" -> ""
           pobs -> "because " ++ pobs ]
           ++ [
    -- "because " ++ show obs,
    s,
    "in"
    ] 
      )
    $ Just sr


prettyShowCtx :: (Map String C.Exp) -> [String]
prettyShowCtx m = prettyShowCtx' $ Map.toList m

prettyShowCtx' [] = []
prettyShowCtx' ((n, C.V e _) : rest)  = prettyShowCtx' rest -- hack to aviod toplevel defs
prettyShowCtx' ((n, e) : rest) = (n++ " := " ++  show (C.e e) ): prettyShowCtx' rest

prettyobs C.Base = "" 
prettyobs (C.Index i o) = prettyobs o ++ "."++ show i 
prettyobs (C.AppW e o) = prettyobs o ++ ".AppW<" ++ show (C.e e) ++">"
prettyobs (C.Aty o) = prettyobs o ++ ".Aty"
prettyobs (C.Bty e o) = prettyobs o ++ ".Bty<" ++ show (C.e e) ++">"
