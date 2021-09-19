{-# LANGUAGE ViewPatterns, DeriveDataTypeable, DeriveGeneric, MultiParamTypeClasses, FlexibleContexts, FlexibleInstances, DeriveFunctor, RankNTypes, LambdaCase  #-}

module Ty where

import Data.Typeable (Typeable)

import GHC.Stack
import Unbound.Generics.LocallyNameless

import Data.Map (Map)
import qualified Data.Map as Map

import Control.Monad.Reader
import Control.Monad.Except ( forM_, MonadError(throwError, catchError) )

import PreludeHelper
import UnboundHelper hiding (Telescope)
import Helper

import Ast
import Env
import Eq -- TODO: parameterize this over a monadic equality? so different falvors of normaization can be swapped in and out? how would annotations work?

import Norm 
import Unification


setRegionFrom :: Exp -> TcMonad a -> TcMonad a
setRegionFrom (Pos s e s') m = setRegion s s' $ setRegionFrom e m 
setRegionFrom _ m = m


-- https://hackage.haskell.org/package/Cabal-3.4.0.0/docs/Distribution-Utils-Generic.html#v:spanMaybe
spanMaybe :: (a -> Maybe b) -> [a] -> ([b],[a])
spanMaybe _ xs@[] =  ([], xs)
spanMaybe p xs@(x:xs') = case p x of
    Just y  -> let (ys, zs) = spanMaybe p xs' in (y : ys, zs)
    Nothing -> ([], xs)


-- unsolved, stuck, constriant -> expanded env, constraints, unsat
unifypat' :: HasCallStack => [(Pat,Ty)] -> [(Pat,Ty)] -> [(Exp, Exp, Ty)] -> TcMonad (TyEnv, [(Exp, Exp, Ty)], [(Exp, Exp)]) 
unifypat' ((PVar x, ty):rest) stuck eqs = do
  logg $ "insert " ++ show x ++ ":" ++ show ty
  logg $ "rest " ++ show rest ++ ", stuck " ++ show stuck ++ ", eqs " ++ show eqs ++ ", "  
  local 
    (\(TyEnv tyCtx dataCtx defCtx,s) -> (TyEnv (Map.insert x ty tyCtx) dataCtx defCtx,s))
    $ unifypat' rest stuck eqs
unifypat' ((Pat dCName args, asNeu -> Just (TCon tCName, tyargs)):rest) stuck eqs = do 
  logg $ "split on " ++ dCName ++ "... :" ++ tCName++ "..."
  logg $ "rest " ++ show rest ++ ", stuck " ++ show stuck ++ ", eqs " ++ show eqs ++ ", "
  DataDef paramtys constructors <- lookupDataDef tCName
  case Map.lookup dCName constructors of
    Nothing  -> throwprettyError $ "dataconstructor and type constructor incompatible, " ++ dCName ++ " ... : " ++ tCName ++ "..."
    Just tel -> do
      let (pats,tys) = expandUntypedPat args tel rest
      let egs' = fmap (\(listty, (ty,tyty)) -> (listty,ty,tyty) ) $ zip tyargs $ withTy tys paramtys
      unifypat' pats stuck (egs' ++ eqs)

unifypat' (p:rest) stuck eqs = do -- otherwise the pattern is stuck
  logg $ "is stuck " ++ show p
  logg $ "rest " ++ show rest ++ ", stuck " ++ show stuck ++ ", eqs " ++ show eqs ++ ", "  
  unifypat' rest (p:stuck) eqs

unifypat' [] [] eqs = do
  (ctx,_) <- ask
  pure (ctx, eqs,[])

unifypat' [] stuck eqs = do --try to unify and get unstuck
  logg $ "try and unstick, unify " ++ show eqs
  logg $ "stuck  " ++ show stuck

  (env', eqs', unsat) <- fOUni' eqs [] []
  logg $ show env'
  local (\ (_,pos) -> (env',pos)) $ do
  -- (env,pos) <- ask
    stuck' <- mapM (\(p,ty) -> do ty' <- safeWhnf ty; pure (p,ty') ) stuck
    logg $ "stuck' " ++ show stuck'
    if stuck' == stuck -- quite inefficient, possibly unsafe
      then pure (env', eqs', unsat)
      else do
        (env'', eqs'', unsat'') <- unifypat' stuck' [] eqs'
        pure (env'', eqs'', unsat ++ unsat'') 

    
fillFresh :: (Alpha b, Alpha c) => Tel Exp b c -> TcMonad [Pat]
fillFresh (NoBnd _) = pure []
fillFresh (TelBnd _ bndRestTel) = do 
  (x, restTel) <- unbind bndRestTel
  ls <- fillFresh restTel
  pure $ (PVar x) :ls


removePat :: [Pat] -> Pat -> TcMonad [Pat]
removePat _ (PVar _) = pure [] -- completely coverd
removePat (pat@(Pat dCName args):rest) sub@(Pat dCName' _) | dCName /= dCName' = do -- no overlap
  rest' <- removePat rest sub
  pure $ pat : rest'
removePat (Pat dCName args:rest) sub@(Pat dCName' args') -- possible overlap
  | dCName == dCName' && length args == length args' = do
    
    logg $ "removePatsPar " ++ show args ++ " " ++ show args' 
    argss <- removePatsPar args args'
    logg $ "removePat " ++ show rest ++ " " ++ show sub 
    rest' <- removePat rest sub
    let out = ((Pat dCName) <$> argss) ++ rest'
    logg $ "out = " ++ show out
    pure out
removePat ((PVar _):rest) sub@(Pat dCName args) = do -- overlap. ( since var covers everythin, we can skip over the rest?)
    (tCName,_) <- lookupDCName dCName
    DataDef _ (Map.toList -> cons) <- lookupDataDef tCName
    splits <- forM cons $ \ (dCName', tel) -> do
      args' <- fillFresh tel
      pure $ Pat dCName' args'
    logg $ "splits = " ++ show splits
    -- removePat (splits ++ rest) sub
    logg $ "removePat " ++ show splits ++ " " ++ show sub
    removePat splits sub
removePat [] _ = pure []
removePat a@(Pat dCName args:rest) sub@(Pat dCName' args') -- possible overlap
  | dCName == dCName' && length args /= length args' = error $ "bad len, removePat " ++ show a ++ " " ++ show sub

removePatsPar :: [Pat] -> [Pat] -> TcMonad [[Pat]]
removePatsPar h s | length h == length s = do
  logg $ "removePatsPar " ++ show h ++ " " ++ show s
  (ans, _) <- removePatsPar' $ zip h s
  pure ans
removePatsPar _ _ = error "unequal len"

-- wildly inefficient, but more granular patterns help the unifier out.... so why not?
removePatsPar' :: [(Pat,Pat)] -> TcMonad ([[Pat]], [[Pat]])
removePatsPar' ((h,s):rest) = do
  (restAns,restHirez) <- removePatsPar' rest
  logg $ "removePat " ++ show [h] ++ " " ++ show s
  some <- removePat [h] s
  logg $ "some = " ++ show some
  
  logg $ "restHirez = " ++ show (restHirez)
  logg $ "combo some restHirez = " ++ show (combo some restHirez)

  logg $ "combo some restHirez ++ (fmap (s:) restAns)  = " ++ show (combo some restHirez ++ (fmap (s:) restAns) )

  pure (combo some restHirez ++ (fmap (s:) restAns), combo (s:some) restHirez)
removePatsPar' [] = pure ([],[[]]) -- TODO right?


removePats :: [[Pat]] -> [[Pat]] -> TcMonad [[Pat]]
removePats orig [] = pure orig
removePats (orig:orest) (x :rest) = do
  rem <- removePatsPar orig x
  rem' <- removePats orest (x :rest)
  removePats (rem ++ rem')  rest
removePats [] _ = pure []

-- TODO std
combo :: [a] -> [[a]] -> [[a]]
combo [] _ = []
combo (h:rest) ls = fmap (h:) ls ++ combo rest ls




nieveComplement :: Pat -> TcMonad [Pat]
nieveComplement (PVar _) = pure []
nieveComplement (Pat dCName args) = do
  (tCName,_) <- lookupDCName dCName
  DataDef _ (Map.toList -> cons) <- lookupDataDef tCName
  let cons' = filter (\ (dCName',_) -> dCName' /= dCName) cons
  others <- forM cons' $ \ (dCName', tel) -> do
    args' <- fillFresh tel
    pure $ Pat dCName' args'
  
  pure $ others ++ undefined

nieveComplements :: [Pat] -> TcMonad [Pat]
nieveComplements [] = pure []


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
 
tyInfer (Case scrutinees (An (Just bndoutTy)) branches) = do
  
  -- logg $ "bndoutTy, " ++ show bndoutTy
  -- TODO: check motive is WF!
  -- TODO also not the most efficient! only needs to whnf the constructors

  -- (unzip -> (scrutinees', struttys)) <- mapM tyInfer scrutinees
  -- logg $ "TODO, check scrutinees against tel"
  tel <- checkTelMaybe scrutinees bndoutTy
  
  -- logg $ "motive, tel," ++ show tel
  
  -- logg $ "TODO, motive is WF"

  -- logg $ "TODO, check branches"
  
-- TODO coverage checking is now seperate
  forM_ branches $ \ (Match bndP) -> do
    -- logg $ "branch, " ++ show bndP
    -- logg "unsafe hack for now"
    (pats, bod) <- unbind bndP
    logg $ "branch, " ++ show pats 
    let (patconstraints, expectedBranchTy) = expandUntypedPat pats tel []
    (env, eqs, unsat) <- unifypat' patconstraints [] []
    -- several optionas are possible,
    --  throws away eqs
      -- logg $ "eqs " ++ show eqs ++ ", unsat " ++ show unsat
    
    local 
      (\(_,s) -> (env,s)) $ do
      -- unify to completion (not sure how safe that is)
      (env', eqs', unsat')  <- fOUni 20 eqs

--   logg $ "insert " ++ show x ++ ":" ++ show ty
      logg $ "eqs' " ++ show eqs' ++ ", unsat' " ++ show unsat'
      local 
        (\(_,s) -> (env',s)) $ do

          -- logg $ show bod
          -- logg $ ":"
          -- logg $ show expectedBranchTy
          -- logg $ "in"
          -- logg $ show env'
          tyCheck bod expectedBranchTy
      
    -- logg $ "remaining eqs, " ++ show eqs
    -- logg $ "remaining unsat, " ++ show unsat
    -- local (\ (_, s) -> (env, s)) $ do

  -- coverage checking
  pats <- forM branches $ \ (Match bndP) -> do
    (pats, bod) <- unbind bndP
    pure pats

  freePat <- forM [1 .. length scrutinees] $ \ _ -> PVar <$> fresh (s2n "_")

  uncoveredPat <- removePats [freePat] pats
  --unfiy away unreachable pats
  uncoveredPat' <- forM uncoveredPat $ \ pats ->  do
    let (patconstraints, expectedBranchTy) = expandUntypedPat pats tel []
    (env, eqs, unsat) <- unifypat' patconstraints [] []
    -- several optionas are possible,
    --  throws away eqs
      -- logg $ "eqs " ++ show eqs ++ ", unsat " ++ show unsat
    
    local 
      (\(_,s) -> (env,s)) $ do
      -- unify to completion (not sure how safe that is)
      (env', eqs', unsat')  <- fOUni 20 eqs

      pure (pats, unsat ++ unsat')
  
  let uncoveredPat'' = filter (\ (_, unsat) -> null unsat) uncoveredPat'
  case uncoveredPat'' of
    (h : _) -> throwprettyError $ "unmatched pat, " ++ show h
    -- ((h,_) : _) -> throwprettyError $ "unmatched pat, " ++ show h
    _ -> pure ()


  let outTy = substsTel bndoutTy scrutinees
  pure (Case scrutinees (An (Just bndoutTy)) branches, outTy)
  
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
  

tyCheck (Case scrutinees (An Nothing) branches) ty = do

  tyInfer $ Case scrutinees (ann $ dummyTellMaybe (length scrutinees) ty) branches 

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

expandUntypedPat :: HasCallStack => 
  (Alpha b1, Alpha b2, Subst Exp b1, Subst Exp b2) =>
  [Pat] -> Tel Exp b1 b2 -> [(Pat, b1)] -> ([(Pat, b1)], b2)
expandUntypedPat [] (NoBnd tyargs) acc = (acc, tyargs) 
expandUntypedPat (h:t) (TelBnd ty bndrest) acc = 
  let rest = substBind bndrest $ toExp h 
  in expandUntypedPat t rest ((h, ty): acc)
expandUntypedPat _ _ _ = error "bad arg len"

ee0 = expandUntypedPat [Pat "subst" []] (TelBnd TyU $ bind x $ NoBnd $ V x) []
  where
    x = s2n "x"

dummyTellMaybe :: (Alpha a) => Int -> a -> Tel Exp (Maybe Ty) a
dummyTellMaybe 0 a = NoBnd a
dummyTellMaybe x a | x > 0 = 
  TelBnd Nothing $ bind (s2n "_") $ dummyTellMaybe (x-1) a

checkTelMaybe :: (Subst Term a, Alpha a) => [Term] -> Tel Exp (Maybe Ty) a 
             ->  TcMonad (Telescope a)
checkTelMaybe [] (NoBnd a) = pure (NoBnd a)
checkTelMaybe (trm : trms) (TelBnd (Just ty) bndRestTel) = do
  (x,restTel) <- unbind bndRestTel
  tyCheck trm ty
  extendDef x trm ty $ do 
    restTel' <- checkTelMaybe trms restTel
    pure $ TelBnd ty $ bind x restTel'
checkTelMaybe (trm : trms) (TelBnd Nothing bndRestTel) = do
  (x,restTel) <- unbind bndRestTel
  (trm', ty) <- tyInfer trm
  extendDef x trm' ty $ do 
    restTel' <- checkTelMaybe trms restTel
    pure $ TelBnd ty $ bind x restTel'
checkTelMaybe tel app = throwprettyError $  " applications do not match type, " ++ show tel ++ "~/~" ++ show app

substsTel :: (Typeable a, Alpha a, Alpha a2,
 Alpha p, Subst a a2, Subst a p, Show a) =>
   Tel a a2 p -> [a] -> p
substsTel (NoBnd a) [] = a
substsTel (TelBnd _ bndRestTel) (x : xs) = 
  substsTel (substBind bndRestTel x) xs
substsTel tel app = error $  " applications do not match type, " ++ show tel ++ "~/~" ++ show app

-- give telescopes their own file
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


