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
import Dynamic.ElabBase
import PreludeHelper
import GHC.TopHandler (runIO)
import AlphaShow (lfullshow)
import Data.Typeable
import Dynamic.Visitor
import Dynamic.Norm (safeWhnf)
import Dynamic.Warning
import Control.Monad.Writer (WriterT (runWriterT))

-- to Elab a full module with fully mutual recirsive definitions we need to elaborate definitions in a "just in time" sort of way
-- this is where the partial module comes in
--TODO: should only rely on the module typeclasses not the specific data



instance (Fresh m, MonadError C.Err m, Monad m, WithSourceLoc m) => (WithDynDefs (ElabMT m)) where
  getDatadef' tcName = ElabMT $ do
    (E.TyEnv{E.dataCtx=dt},config) <- ask
    case Map.lookup tcName dt of
      Nothing -> pure Nothing
      Just (DataDef _ cons) -> do
        -- mtel <- unElabMT $ getTConnTel' tcName
        -- case mtel of
        --   Nothing  -> pure Nothing  
        --   Just tel -> do
       -- get the elements in a way that will elaborate them if they are not already
        tel <- unElabMT $ getTConnTel tcName
        consls <- forM (Map.toList cons) $ \ (dCName, _) -> do
          (_ , contel) <- unElabMT $ getConsTcon dCName
          pure (dCName, contel)
        pure $ Just $ C.DataDef tel $ Map.fromList consls 
 --  getDatadef

  getTConnTel tConn = ElabMT $ do
    PartialModule{tCons=pc}<- get 
    case Map.lookup tConn pc of
      Just xx -> pure xx
      Nothing -> do
        (E.TyEnv{E.dataCtx=dt},config) <- ask
        case Map.lookup tConn dt of
          Nothing -> throwPrettyError $ "could not find def of type constructor '" ++ tConn ++ "'"
          Just (DataDef tel _) -> do
            tel' <- unElabMT $ elabTelUnit tel $ initElabInfo config 
            modify $ \ pm@PartialModule{tCons=pc'} -> pm{tCons=Map.insert tConn tel' pc'}
            pure tel'

  getConsTcon' dCName = ElabMT $ do
    (E.TyEnv{E.dataCtx=dt},config) <- ask
    case filter (\ (tCname, DataDef _ dd) -> Map.member dCName dd) $ Map.toList dt of
      [(tCname, DataDef _ dcons)] -> do
        telTys <- unElabMT $ getTConnTel tCname -- make sure the tc is resolved
        PartialModule{dCons=pdc} <- get
        case Map.lookup tCname pdc >>= Map.lookup dCName of
          Just xx -> pure $ Just (tCname, xx)
          Nothing -> do
            let (Just tel) = Map.lookup dCName dcons
            tel' <- unElabMT $ elabTelLs tel telTys $ initElabInfo config
            modify $ \ pm@PartialModule{dCons=pdc'} -> pm{dCons=instertsert tCname dCName tel' pdc'}
            pure $ Just (tCname, tel')
      _ -> pure Nothing


  getDefnTy' x = ElabMT $ do
    PartialModule{refTys=dfnty} <- get 
    case Map.lookup x dfnty of
      Just ty -> pure $ Just ty
      Nothing -> do
        (E.TyEnv{E.defCtx=defn},config) <- ask
        case Map.lookup x defn of
          Nothing -> pure Nothing  
          Just (_,ty) -> do
            ty' <- unElabMT $ elabCast ty C.TyU $ initElabInfo config
            modify $ \ pm@PartialModule{refTys=dfnty'} -> pm{refTys= Map.insert x ty' dfnty'}
            pure $ Just ty'

  getDefn' x = ElabMT $ do
    PartialModule{refDefs=dfn} <- get
    case Map.lookup x dfn of
      Just trm -> pure $ Just trm
      Nothing -> do
        mxty <- unElabMT $ getDefnTy' x
        case mxty of
          Nothing -> pure Nothing 
          Just ty -> do
            (E.TyEnv{E.defCtx=defn},config) <- ask
            let Just (trm,_) = Map.lookup x defn
            -- loggg ""
            -- loggg "getDefn'"
            -- loggg $ "x = " ++ x
            -- loggg $ "ty = " ++ lfullshow ty
            def <- unElabMT $ elabCast trm ty $ initElabInfo config
            modify $ \ pm@PartialModule{refDefs=dfnty'} -> pm{refDefs= Map.insert x def dfnty'}
            pure $ Just def

elabTelUnit ::  (Fresh m, MonadError C.Err m, WithDynDefs m, WithSourceLoc m) => Tel Term Ty () -> (ElabInfo m) -> m (Tel C.Term C.Ty ())
elabTelUnit (NoBnd ()) _ = pure $ NoBnd ()
elabTelUnit (TelBnd ty bndbod) ctx = do
  ty' <- elabCast ty C.TyU ctx
  (x, bod) <- unbind bndbod
  (x', ctx') <- setVar x ty' ctx
  bod' <- elabTelUnit bod ctx'
  pure $ TelBnd ty' $ bind x' bod'

--elabTelLs :: (Fresh m, MonadError C.Err m, MonadWithDynDefs m) => Tel Term Ty [Exp] -> Tel C.Term C.Ty () -> Ctx -> VMap -> m (Tel C.Term C.Ty [C.CastExp])
elabTelLs
  :: (Fresh m, MonadError C.Err m, WithDynDefs m, WithSourceLoc m) =>
     Tel Term Exp [Exp]
     -> Tel C.Term C.Ty ()
     -> (ElabInfo m)
     -> m (Tel C.Term C.Exp [C.Exp])
-- elabTelLs = error "working on it"
elabTelLs (NoBnd params) telltys ctx = do
  params' <- elabCastTelUnit params telltys ctx
  pure $ NoBnd params'
elabTelLs (TelBnd ty bndbod) telltys ctx  = do
  ty' <- elabCast ty C.TyU ctx
  (x, bod) <- unbind bndbod
  (x', ctx') <- setVar x ty' ctx
  bod' <- elabTelLs bod telltys ctx'
  pure $ TelBnd ty' $ bind x' bod'

-- | run in an empty module
rem' :: ElabMT (WithSourceLocMT (FreshMT (ExceptT e Identity))) a -> E.TyEnv -> Either e (a, PartialModule)
rem' e env = runIdentity $ runExceptT $ runFreshMT $ runWithSourceLocMT' $ runElabMT e env emp


rem e env s = runIdentity $ runExceptT $ runFreshMT $ runWithSourceLocMT (runElabMT e env emp) s

-- remIO e env s = runIO $ runFreshMT $ runWithSourceLocMT (runElabMT e env emp) s


emp = PartialModule Map.empty Map.empty Map.empty Map.empty


instertsert :: (Ord k1, Ord k2) => k1 -> k2 -> v -> Map k1 (Map k2 v) -> Map k1 (Map k2 v)
instertsert k1 k2 v m = 
  case Map.lookup k1 m of
    Nothing -> Map.insert k1 (Map.singleton k2 v) m
    Just mm -> Map.insert k1 (Map.insert k2 v mm) m

-- Elab the full module, a little hacky TODO: should only rely on the module typeclasses not the specific data
-- elabmodule' :: E.TyEnv -> Either
--      C.Err ((Map TCName C.DataDef, Map C.Var C.Term), PartialModule)
-- elabmodule' :: E.TyEnv -> Either C.Err (Module, PartialModule)
-- elabmodule' src = elabmodule src Nothing rem


elabmodule src range = do
  (m, _) <- runWithSourceLocMT (runElabMT (elabmodule' src) src emp) range
  pure m


-- elabmodule'IO src = elabmodule src Nothing remIO

elabmodule' :: (WithDynDefs m, WithSourceLoc m, MonadError C.Err m) => E.TyEnv -> m Module
elabmodule' src@(E.TyEnv{E.dataCtx=dt, E.defCtx=dfns}) = do
  -- logg $  "dfns=" ++ show dfns
  let dfnRefs = fmap fst $ Map.toList dfns
  -- -- mapM_ (\ x -> elabdfnVar' x src) dfnVars

  let tCnames = fmap fst $ Map.toList dt
  mapM_ (\ x -> getTConnTel x) tCnames

  let dCnames = concat $ fmap (\ (_, (DataDef _ cons)) -> Map.keys cons  ) $ Map.toList  dt
  mapM_ (\ x -> getConsTcon' x) dCnames

  mapM_ (\ x -> getDefnTy' x ) dfnRefs
  mapM_ (\ x -> getDefn' x ) dfnRefs

  termdefns <- mapM (\ x -> do
    def <- getDefn x 
    ty <- getDefnTy x 
    pure (x,(def,ty))
    ) dfnRefs

  datadefls <- mapM (\ x -> do def <- getDatadef x; pure (x,def) ) tCnames

  pure (Module {dataCtx=Map.fromList datadefls, defCtx=DefCtx $ Map.fromList termdefns})
  

-- | run under a surface language module, without source info
rununder' :: ElabMT (WithSourceLocMT ( FreshMT (ExceptT C.Err Identity))) a -> E.TyEnv -> Either C.Err (a, PartialModule)
rununder' e src@(E.TyEnv _ dt dfns) = rem' (do
  let dfnRefs = fmap fst $ Map.toList dfns
  -- -- mapM_ (\ x -> elabdfnVar' x src) dfnVars

  let tCnames = fmap fst $ Map.toList dt
  mapM_ (\ x -> getTConnTel x) tCnames

  let dCnames = concat $ fmap (\ (_, (DataDef _ cons)) -> Map.keys cons  ) $ Map.toList  dt
  mapM_ (\ x -> getConsTcon' x) dCnames

  mapM_ (\ x -> getDefnTy' x ) dfnRefs
  mapM_ (\ x -> getDefn' x ) dfnRefs

  termdefns <- mapM (\ x -> do
    def <- getDefn x 
    ty <- getDefnTy x 
    pure (x,(def,ty))
    ) dfnRefs

  datadefls <- mapM (\ x -> do def <- getDatadef x; pure (x,def) ) tCnames

  pure  (Map.fromList datadefls, Map.fromList termdefns)

  e
    )  src

-- an elaborated version of the stdlib
stdlib :: Module
stdlib = modul
  where
    Right modul  = runIdentity $ runExceptT $ runFreshMT $ elabmodule E.stdlib Nothing 




Right stdlibIO' = runIdentity $ runExceptT $ runFreshMT $ elabmodule E.stdlib Nothing



stdlibIO'' :: Module
stdlibIO'' = runFreshM $ visitModule stdlibIO'  (visitFresh visitorCleanSameDef)


stdlibwarns :: [Warning]
stdlibIO :: Module
(stdlibIO, stdlibwarns) = rwf $ visitModule stdlibIO'' (visitFresh visitorWarnSame) 

-- rwf :: Monoid w => FreshMT (WriterT w Identity) a -> (a, w)
-- rwf e = runIdentity $ runWriterT $ runFreshMT $ e
-- eq 

visitModule m@(Module {dataCtx=dataCtx, defCtx= DefCtx (Map.toList -> defCtx)}) w = runWithModuleMT (do
  dataCtx' <- forM (Map.toList dataCtx) $ \ (tcname, C.DataDef tel (Map.toList -> cdefs)) -> do
    tel' <- visitTelU tel w
    cdefs' <- forM cdefs $ \ (dcname, ctel) -> do 
      ctel' <- visitTelE ctel w 
      pure (dcname, ctel') 
    
    pure (tcname, C.DataDef tel' (Map.fromList cdefs'))
  
  defCtx' <- forM defCtx $ \ (tcname, (trm,ty)) -> do
    trm' <- w trm
    ty' <- w ty
    pure (tcname, (trm', ty'))

  pure $ Module (Map.fromList dataCtx') (DefCtx $ Map.fromList defCtx')) m


-- visitTelU :: (Typeable n, Fresh f, Alpha t,
--   Alpha a) =>
--   Tel n t () -> (t -> f a) -> f (Tel n a ())
visitTelU :: (Fresh m) => Tel C.Term C.Ty () -> (C.Term -> m C.Term ) -> m (Tel C.Term C.Ty ()) 
visitTelU (NoBnd ()) w = pure $ NoBnd ()
visitTelU (TelBnd ex bndRest) w = do
  ex' <- w ex
  (x,rest) <- unbind bndRest
  rest' <- visitTelU rest w
  pure $ TelBnd ex' $ bind x rest'


visitTelE :: (Fresh m) => Tel C.Term C.Ty [C.Term]  -> (C.Term -> m C.Term) -> m (Tel C.Term C.Ty [C.Term] ) 
visitTelE (NoBnd e) w = do
  e' <- mapM w e
  pure $ NoBnd e'
visitTelE (TelBnd ex bndRest) w = do
  ex' <- w ex
  (x,rest) <- unbind bndRest
  rest' <- visitTelE rest w
  pure $ TelBnd ex' $ bind x rest'

-- visitorWarnSame
-- data DataDef = DataDef (Tel Term Ty ()) (Map DCName (Tel Term Ty [Term])) deriving (
--   -- Show, 
--   Generic, Typeable)