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
import Dynamic.ElabBase
import Dynamic.Norm
import Control.Monad.RWS (MonadWriter)
import Control.Monad.Writer
import Control.Monad (MonadPlus)
import Control.Monad.Fix (MonadFix)

-- machinery to translate module definitions from the surface language into the core languguage
-- TODO seperate the dynamic stuff (needed for reading acuatual files) from the static stuff (good for testing)


makeMod :: Map TCName C.DataDef -> Map C.RefName (C.Term,C.Ty) -> Module
makeMod ddefs trmdefs = Module ddefs (DefCtx trmdefs)

emptyModule :: Module
emptyModule = Module Map.empty (DefCtx Map.empty)

underModule :: (Subst Exp a) => a -> Module -> a
underModule e (Module {dataCtx=Map.toList-> dataLs,defCtx= DefCtx (Map.keys-> defls)}) = 
  underRefs (underData e dataLs) defls

underRefs :: Subst Exp a => a -> [String] -> a
underRefs e ls = substs ((\r -> (s2n r,Ref r))<$>ls)e

underData :: Subst Exp t => t -> [(TCName, C.DataDef)] -> t
underData e [] = e
underData e ((tCname, C.DataDef _ (Map.toList-> ls)) : rest) = 
  subst (s2n tCname) (TCon tCname) $ underConstructors' (underData e rest) (fst <$> ls) 

underConstructors' :: Subst Exp t => t -> [DCName] -> t
underConstructors' e [] = e
underConstructors' e (dCname : rest) = subst (s2n dCname) (DCon dCname) $ underConstructors' e rest




data Config = Config  {
    whnf :: forall m. (Fresh m, WithDynDefs m )=>  C.Term -> m C.Term
  }

defualtConfigConfig :: Config
defualtConfigConfig = Config{
    Dynamic.Env.whnf= safeWhnf 1000
  }

initElabInfo :: (Fresh m, WithDynDefs m ) =>  Config -> ElabInfo m
initElabInfo (Config{Dynamic.Env.whnf=whnf}) = ElabInfo Map.empty Map.empty Map.empty whnf






-- a fancy reader that contains a static module
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

-- TODO: double check
instance (MonadReader r m) => (MonadReader r (WithModuleMT m)) where
  ask = lift ask
  local f ma = do
    a <- ma
    lift $ local f $ pure a

instance (MonadWriter w m) => (MonadWriter w (WithModuleMT m)) where
  tell = lift . tell
  listen = error "not done yet"
  pass = error "not done yet"
  
instance (Fresh m, Monad m) => (WithDynDefs (WithModuleMT m)) where
  getDatadef' tcName = WithModuleMT $ do
    Module{dataCtx=dataCtx} <- ask
    pure $ Map.lookup tcName dataCtx

  getConsTcon' dCName =  WithModuleMT $ do
    Module{dataCtx=dataCtx} <- ask
    case filter (\ (tCname, C.DataDef _ dd) -> Map.member dCName dd) $ Map.toList dataCtx of
      [(tCname, C.DataDef _ dcons)] -> do
        let Just tel = Map.lookup dCName dcons
        pure $ Just (tCname, tel)
      _ -> pure Nothing 

  getDefn' x = WithModuleMT $ do
    Module{defCtx=(DefCtx defCtx)} <- ask
    case Map.lookup x defCtx of
      Nothing -> pure Nothing 
      Just (def,_) -> pure $ Just def

  getDefnTy' x =  WithModuleMT $ do
    Module{defCtx=(DefCtx defCtx)} <- ask
    case Map.lookup x defCtx of
      Nothing -> pure Nothing 
      Just (_,ty) -> pure $ Just ty

-- TODO add Elab info as a reader
-- newtype ElabMT m a = ElabMT {unElabMT :: ReaderT (ElabInfo m) ... (StateT PartialModule m) a}

-- Config


-- the elaboration monad, has a surface language module(E.TyEnv) availible to look up definitions
newtype ElabMT m a = ElabMT {unElabMT :: ReaderT (E.TyEnv, Config) (StateT PartialModule m) a}
  deriving
    ( Functor
    , Applicative
    , Alternative
    , Monad
    , MonadIO
    , MonadPlus
    , MonadFix
    )

runElabMT :: ElabMT m a -> E.TyEnv -> PartialModule -> m (a, PartialModule)
runElabMT e env s = runStateT (runReaderT (unElabMT e) (env, defualtConfigConfig)) s

instance MonadTrans ElabMT where
  lift = ElabMT . lift . lift

instance (Fresh m) => (Fresh (ElabMT m)) where
  fresh = lift . fresh

instance (MonadError e m) => (MonadError e (ElabMT m)) where
  throwError = lift . throwError
  catchError m h = error "not done yet"
--m h = FreshMT $ EC.catchError (unFreshMT m) (unFreshMT . h)

instance (WithSourceLoc m) => (WithSourceLoc (ElabMT m)) where
  localSourceRange s ma = let
    ee e p = localSourceRange s $ runStateT (runReaderT (unElabMT ma) e) p
    in ElabMT $ ReaderT $ \ty ->  StateT $ ee ty -- TODO could be substantially prettier

  askSourceRange = lift askSourceRange





throwInfoError :: HasCallStack => (MonadError C.Err m) => String -> C.Info -> m b
throwInfoError s (C.Info {C.sr=sr, C.obs=obs}) = do
  runWithSourceLocMT (throwPrettyError $ unlines $
    ["",
    --   show (C.e $ unignore l) ++ " =/= " ++  show (C.e $ unignore r)
    -- ] ++ (case prettyShowCtx ctx of
    --        [] -> []
    --        pctx -> "since when " : pctx  )
    --   ++ [case prettyobs obs of
    --        "" -> ""
    --        pobs -> "because " ++ pobs ]
    --        ++ [
    "because " ++ show obs,
    s,
    "in"
    ] 
      )
    $ sr
