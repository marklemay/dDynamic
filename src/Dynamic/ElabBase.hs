
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

module Dynamic.ElabBase where

import Prelude hiding (head)
  
import GHC.Stack

import Data.Typeable (Typeable)
import GHC.Generics (Generic)


import Ast
import qualified Env as E
import qualified Dynamic.Ast as C
import qualified Dynamic.Err as C
-- import qualified Dynamic.Env as C --TODO clean
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
import PreludeHelper
import SourcePos
import Control.Applicative
import Control.Monad.Reader
    ( ReaderT(..), MonadReader(ask, local) )
import Control.Monad.State
import Control.Monad (MonadPlus)
import Control.Monad.Fix (MonadFix)

-- this file exsts becuase GHC is bad aobut cyclic module depndnecies!

-- TODO perhaps readerize this?
data ElabInfo m = ElabInfo  {
    varMap :: Map Var C.Var,
    tyCtx :: Map C.Var C.Ty,
    assign :: Map C.Var (C.Term, C.Ty, C.EqEv), -- invarient: assinments must never contain their own vars
    
    whnf :: C.Term -> m C.Term
    -- this will be run a lot, so probly limit it
    -- solution from pattern matching
  }deriving Generic 
  
instance Show (ElabInfo m) where
  -- show _ = "ElabInfo{..}"
  show (ElabInfo{tyCtx=tyCtx,assign=assign}) = "ElabInfo{tyCtx=" ++ show tyCtx ++",assign="++ show assign ++"..}"



-- instance Alpha (ElabInfo m) where-- hack for debugging
--   aeq' actx l r =  error "not yet implemented"  
--   fvAny' actx nfn sa=  error "not yet implemented"  
--   open actx npath=  error "not yet implemented"  
--   isPat   =  error "not yet implemented"  
--   isTerm    =  error "not yet implemented"  
--   isEmbed     =  error "not yet implemented"  
--   nthPatFind      =  error "not yet implemented"  
--   namePatFind       =  error "not yet implemented"  
--   swaps'       =  error "not yet implemented"  
--   lfreshen'       =  error "not yet implemented"  
--   acompare' =  error "not yet implemented"  
--   freshen' =  error "not yet implemented"   
--   has' =  error "not yet implemented"  
-- instance AlphaLShow (ElabInfo m) where
--   aShow _ info = pure (Set.empty, show info) -- hack for debugging

empElabInfo :: (C.Term -> m C.Term) -> ElabInfo m
empElabInfo = ElabInfo Map.empty Map.empty Map.empty

empTestElabInfo :: Monad m => ElabInfo m
empTestElabInfo = empElabInfo $ \ x-> do
  logg "not normalizing for testing"
  pure x

getVar x info = 
  case (Map.lookup x $ varMap info) of
    (Just x') ->
      case Map.lookup x' $ tyCtx info of
        (Just ty) -> Just (x', ty)
        _ -> Nothing
    _ -> Nothing

getVar' :: Var -> ElabInfo m -> C.Var
getVar' x info = 
  case (Map.lookup x $ varMap info) of
    (Just x') -> x'

    
setVar :: Fresh m1 =>
  Name Term -> C.Ty -> ElabInfo m2 -> m1 (Name C.Term, ElabInfo m2)
setVar x ty info@(ElabInfo {varMap=varMap, tyCtx=tyCtx}) = do
  x' <- fresh $ s2n $ name2String x
  pure $ (x', info {varMap= (Map.insert x x' varMap), tyCtx=(Map.insert x' ty tyCtx)})

data Equation = Equation{
  left :: C.Term,
  -- leftTy :: Ty,
  right :: C.Term,
  sameTy :: C.Ty,
  why :: C.EqEv
} deriving (Generic, Typeable)



type TyCtx = Map Var Ty
type DataCtx = Map TCName C.DataDef

-- | For toplevel term definitions
newtype DefCtx = DefCtx (Map C.RefName (C.Term,C.Ty)) -- TODO  (Maybe C.Term,C.Ty)
  deriving (Generic, Typeable)
instance Alpha DefCtx
instance AlphaLShow DefCtx
instance Show DefCtx where
  show = lfullshow

data PartialModule = PartialModule {
  tCons :: Map TCName (Tel C.Term C.Ty ()), 
  dCons :: Map TCName (Map DCName (Tel C.Term C.Ty [C.Ty])), 
  refDefs :: Map RefName C.Ty, 
  refTys :: Map RefName C.Term
  }
  deriving Show

data Module = Module {dataCtx::DataCtx, defCtx::DefCtx}
  deriving (Generic, Typeable)
instance Alpha Module
instance AlphaLShow Module
instance Show Module where
  show = lfullshow


-- a interface to get partial module info out of the environment
class (Monad m) => WithDynDefs m where 
   getDatadef' :: TCName -> m (Maybe C.DataDef)
   getDatadef :: (WithSourceLoc m, MonadError C.Err m) => TCName -> m C.DataDef
   getDatadef tCName = do
     mdef <- getDatadef' tCName
     case mdef of 
       Nothing -> throwPrettyError $ "tCName not found " ++ tCName
       Just def -> pure def

  --  getTConnTel' :: (WithSourceLoc m, MonadError C.Err m) => TCName -> m (Maybe (Tel C.Term C.Ty ()))
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
       
   getDefnTy' :: RefName -> m (Maybe C.Ty)

   getDefn' :: RefName -> m (Maybe C.Term)
   getDefn :: (WithSourceLoc m, MonadError C.Err m) => RefName -> m C.Term
   getDefn x = do
     mx <- getDefn' x
     case mx of
       Just ans -> pure ans 
       Nothing ->  throwPrettyError $  "ref not found " ++ show x
       
   getDefnTy :: (WithSourceLoc m, MonadError C.Err m) => RefName -> m C.Ty
   getDefnTy x = do
     mx <- getDefnTy' x
     case mx of
       Just ans -> pure ans 
       Nothing ->  throwPrettyError $  "ref not found " ++ show x


instance (WithDynDefs m) => (WithDynDefs (ReaderT r m)) where
  getDatadef' = lift . getDatadef' 
  getConsTcon' = lift . getConsTcon'
  getDefn' = lift . getDefn' 
  getDefnTy' = lift . getDefnTy'

instance (WithDynDefs m) => (WithDynDefs (FreshMT m)) where
  getDatadef' = lift . getDatadef' 
  getConsTcon' = lift . getConsTcon'
  getDefn' = lift . getDefn' 
  getDefnTy' = lift . getDefnTy'

instance (WithDynDefs m) => (WithDynDefs (ExceptT e m)) where
  getDatadef' = lift . getDatadef' 
  getConsTcon' = lift . getConsTcon'
  getDefn' = lift . getDefn'
  getDefnTy' = lift . getDefnTy'

instance (WithDynDefs m) => (WithDynDefs (StateT r m)) where
  getDatadef' = lift . getDatadef' 
  getConsTcon' = lift . getConsTcon'
  getDefn' = lift . getDefn' 
  getDefnTy' = lift . getDefnTy'


--TODO belongs somewhere else?
class (Monad m) => WithSourceLoc m where
  localSourceRange :: SourceRange -> m a -> m a
  -- TODO make this properly local?

  askSourceRange :: m (Maybe SourceRange)




localSourceRangeFrom :: WithSourceLoc m  => Ast.Exp -> m a -> m a
localSourceRangeFrom (Pos l e r) ma = do
  sr <- askSourceRange
  case sr of
    Just (SourceRange msrc _ _) -> localSourceRange (SourceRange msrc l r) $ localSourceRangeFrom e ma
    Nothing -> localSourceRange (SourceRange Nothing l r) $ localSourceRangeFrom e ma
localSourceRangeFrom _ ma = ma

localSources :: WithSourceLoc m  => SourcePos -> SourcePos -> m a -> m a
localSources l r ma = do
  sr <- askSourceRange -- asks to repair possibly broke string
  case sr of
    Just (SourceRange msrc _ _) -> localSourceRange (SourceRange msrc l r) ma
    Nothing -> localSourceRange (SourceRange Nothing l r) ma

throwPrettyError :: HasCallStack => (WithSourceLoc m, MonadError C.Err m) => String -> m b
throwPrettyError s = do
  sr <- askSourceRange
  throwError $ C.Msg s sr



prettyShowCtx :: (Map String C.Exp) -> [String]
prettyShowCtx m = prettyShowCtx' $ Map.toList m

prettyShowCtx' [] = []
-- prettyShowCtx' ((n, C.V e _) : rest)  = prettyShowCtx' rest -- hack to aviod toplevel defs
-- prettyShowCtx' ((n, e) : rest) = (n++ " := " ++  show (C.e e) ): prettyShowCtx' rest

-- prettyobs C.Base = "" 
-- prettyobs (C.Index i o) = prettyobs o ++ "."++ show i 
-- prettyobs (C.AppW e o) = prettyobs o ++ ".AppW<" ++ show (C.e e) ++">"
-- prettyobs (C.Aty o) = prettyobs o ++ ".Aty"
-- prettyobs (C.Bty e o) = prettyobs o ++ ".Bty<" ++ show (C.e e) ++">"



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


instance (Fresh m) => (Fresh (WithSourceLocMT m)) where
  fresh = lift . fresh

instance (MonadError e m) => (MonadError e (WithSourceLocMT m)) where
  throwError = lift . throwError
  catchError m h = error "not done yet"
--m h = FreshMT $ EC.catchError (unFreshMT m) (unFreshMT . h)

-- TODO: double check
instance (MonadReader r m) => (MonadReader r (WithSourceLocMT m)) where
  ask = lift ask
  local f ma = do
    a <- ma
    lift $ local f $ pure a

instance WithDynDefs m => WithDynDefs (WithSourceLocMT m) where
  getDatadef' = lift . getDatadef'
  getConsTcon' = lift . getConsTcon'
  getDefnTy' = lift . getDefnTy' 
  getDefn' = lift . getDefn'