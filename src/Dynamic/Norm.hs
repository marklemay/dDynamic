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

module Dynamic.Norm where

import GHC.Stack ( HasCallStack )


import Control.Applicative (Applicative (..), (<$>))
import Control.Monad (guard)
import Data.List (find)


import Data.Map (Map)
import qualified Data.Map as Map

import Data.Set (Set)
import qualified Data.Set as Set

import Data.Monoid (Any (..))
import Data.Typeable (Typeable)
import GHC.Generics (Generic, U1 (U1))
import Unbound.Generics.LocallyNameless
import Control.Monad.Except
import Unbound.Generics.LocallyNameless.Unsafe (unsafeUnbind)
import Control.Monad.Reader

import PreludeHelper
import UnboundHelper
import AlphaShow
import SourcePos

import Dynamic.Ast
import Dynamic.Err
import Unbound.Generics.LocallyNameless.Bind
import Control.Monad.State
import Dynamic.ElabBase hiding (whnf)
import Norm (isVal)
import Control.Exception hiding (assert)
import GHC.IO.Encoding.Latin1 (mkLatin1_checked)



data Next m = Next {
  -- chkN :: (Exp -> Info -> EqEv -> Exp -> m Exp),
  critN :: Exp -> m Exp
  ,
  -- critEv :: (Exp -> m Exp),
  -- critApp :: (Exp -> m Exp),
  -- critCast :: (Exp -> m Exp),
  after :: (Exp -> m Exp),
  assert :: Exp -> Info -> EqEv -> Exp ->  m Exp
  ,
  unmatched :: Exp -- orig expression (TODO probly remove this at some point)
  -> [Exp] -- scrutninees
  -> Maybe ([[Pat]], Maybe SourceRange) -- warning info
  -> m Exp
  }

noNext :: Applicative m => Next m
noNext = Next{
  -- chkN :: (Exp -> Info -> EqEv -> Exp -> m Exp),
  critN = pure
  ,
  -- critEv :: (Exp -> m Exp),
  -- critApp :: (Exp -> m Exp),
  -- critCast :: (Exp -> m Exp),
  after = pure,
  assert = \ l info ev r -> pure $ Same l info ev r,
  
  unmatched = \ e _ _ -> pure e
  }

-- evidence guarded norm, doesn't get stuck in the empty ctx
norm ::
  HasCallStack => 
  (Fresh m) => 
  Next m ->
  Exp -> 
  m Exp
norm next (C u ev) = do
  ev' <- critN next ev
  case ev' of
    TyU -> critN next u
    TConF _ _ (NoBnd ()) _ -> do
      u' <- critN next u
      case u' of
        (C u'' ev'') ->  critN next $ C u'' $ Union ev'' TyU ev' 
        _ -> pure (C u' ev')
        -- (u'', Just ev') -> do
        --   ev'' <- critN next $ Union ev' TyU ev 
        --   pure (C u'' ev'') -- is impossible for this to be TyU, so this is the final form
    -- Pi _ _ -> pure (C u ev')
    _ -> pure (C u ev')
norm next (Same l info ev r) = do
  ev' <- critN next ev
  case ev' of
    TyU -> do
      l' <- critN next l
      r' <- critN next r
      case (l', r') of
        (TyU , TyU) -> pure TyU
        (Pi la blBod , Pi ra brBod) -> do
          (lName, lbod) <-unbind blBod
          let rbod = substBind brBod (V lName)
          -- xx <- unbind2 blBod brBod
          a <- assert next la (argInfo info) TyU ra
          bod <- assert next lbod (bodInfo (V lName) info) TyU rbod
          pure $ Pi a $ bind lName bod
        (zipTConM (\l i ev r -> assert next l (tconInfo i info) ev r) -> Just ans) -> ans
        _ -> assert next l' info ev' r'
    TConF _ _ (NoBnd ()) _ -> do
      l' <-  critN next l
      r' <-  critN next r --little redundant work
      case (l', r') of
        (C l'' lev, _) -> critN next $ (Same l'' info (Union lev TyU ev') r') 
        (_, C r'' rev) -> critN next $ (Same l' info (Union ev' TyU rev) r'') 
        (zipDConM (\l i ev r -> assert next l (dconInfo i info) ev r) (\l i ev r -> assert next l (tconInfo i info) ev r) -> Just ans) -> do
          ans' <- ans
          pure $ C ans' ev'
        _ -> assert next l' info ev' r'
    _ -> pure $ Same l info ev' r 
    -- _ -> pure $ assert next l info ev' r 
norm next (Union l ev r) = do
  ev' <- critN next ev
  case ev' of
    TyU -> do
      l' <- critN next l
      r' <- critN next r
      case (l', r) of
        (TyU , TyU) -> pure TyU
        (Pi la blBod , Pi ra brBod) -> do
          (lName, lbod) <-unbind blBod
          let rbod = substBind brBod (V lName)
          -- xx <- unbind2 blBod brBod
          pure $ Pi (Union la  TyU ra) $ bind lName (Union lbod  TyU rbod)
        (zipTCon (\l i ev r -> Union l  ev r) -> Just ans) -> pure ans
        _ -> pure (Union l' ev' r')
    TConF _ _ (NoBnd ()) _ -> do
      l' <-  critN next l
      r' <-  critN next r --little redundant work
      case (l', r') of
        (C l'' lev, _) -> critN next $ (Union l'' (Union lev TyU ev') r') 
        (_, C r'' rev) -> critN next $ (Union l' (Union ev' TyU rev) r'') 
        (zipDCon (\l i ev r -> Union l ev r) (\l i ev r -> Union l ev r) -> Just ans) -> do
          pure $ C ans ev'
        _ -> pure (Union l' ev' r')
    _ -> pure (Union l ev' r)
norm next (f `App` a) = do
  f' <- critN next f 
  case f' of
    Fun bndbndbod -> do
      ((funName, aName), bod) <- unbind bndbndbod
      critN next $ subst aName a bod
      
    TConF tCName inds (TelBnd _ bndrest) tell -> pure $ TConF tCName (inds ++ [a]) (substBind bndrest a) tell
    DConF dCName inds (tCName, TelBnd _ bndrest) tell tellty -> pure $ DConF dCName (inds ++ [a]) (tCName, (substBind bndrest a)) tell tellty
-- TConF,DConF
    C tm (Pi arTy bndbodTy) -> do
      -- (aName, bodTy) <- unbind bndbodTy
      let ac = C a arTy
      critN next $ C (tm `App` ac) $ substBind bndbodTy ac
    Same l info (Pi arTy bndbodTy) r -> do
      let ac = C a arTy
      critN next $ Same (l `App` ac) (appInfo ac info) (substBind bndbodTy ac) (r `App` ac)
    Union l (Pi arTy bndbodTy) r -> do
      let ac = C a arTy
      critN next $ Union (l `App` ac) (substBind bndbodTy ac) (r `App` ac)

    _ -> pure $ f' `App` a

norm next (Tind i ev) = do
  ev' <- critN next ev
  case ev' of
    TConF _ inds (NoBnd ()) _ | i < (fromIntegral $ length inds) -> critN next $ inds !! fromIntegral i -- a little broke at large ind
    _  -> pure $ Tind i ev'

norm next (Dind i ev) = do
  ev' <- critN next ev
  case ev' of
    DConF _ args (_, NoBnd _) _ _ | i < (fromIntegral $ length args) -> critN next $ args !! fromIntegral i
    C (DConF _ args (_, NoBnd _) _ _) (TConF _ _ (NoBnd ()) _)| i < (fromIntegral $ length args) -> critN next $ args !! fromIntegral i -- duble chack that this is acounted for formally
    _  -> pure $ Dind i ev'
norm next e@(Case scrutinees branches (An ann)) = do
  ans <- matches next scrutinees branches
  case ans of
    Right e' -> do
      -- logg "return from case"
      -- loggg $ lfullshow e'
      critN next $ e'
    Left (scrutinees', []) -> unmatched next e scrutinees' ann
    Left _ -> pure e -- don't try to simplify the scrutinees/branches yet
-- norm next (Blame ev) = undefined
-- norm next x = pure x
norm next e@(V{}) = pure e
norm next e@(Ref{}) = pure e
norm next e@(Fun{}) = pure e
norm next e@(Pi{}) = pure e
norm next e@(TConF{}) = pure e 
norm next e@(DConF{}) = pure e
-- norm next e@(TConF{}) = after next $ e -- kind of a hack, should properly have a simplification funciont that is applied to sub terms
-- norm next e@(DConF{}) = after next $ e
norm next e@(TyU) = pure e
norm next e@(Blame{}) = pure e



match :: 
  HasCallStack => 
  (Subst Exp a, Fresh m) => 
  Next m -> [(Exp,Pat)] -> a -> m (YesNoStuck a)
match next []  bod = pure $ Yes bod
match next ((e, PVar x):ms) bod = do 
  match next ms $ subst x e bod
match next ((e, Pat dcName pats evName): ms) bod = do --TODO can perhaps remove tCName
  e' <- norm next e
  case e' of 
    -- overly conservative
    -- C (DConF dcName' args (_, NoBnd _) _ _) ev@(TConF _ _ (NoBnd _) _) | length args == length pats && dcName' == dcName -> match next (zip args pats ++ ms) $ subst evName ev bod
    
    -- cbv will check ev suffuciently, whnf doesn't need to be checked
    C (DConF dcName' args (_, NoBnd _) _ _) ev | length args == length pats && dcName' == dcName -> match next (zip args pats ++ ms) $ subst evName ev bod

    DConF dcName' args (tCName', NoBnd inds) _ tytel | length args == length pats && dcName' == dcName -> 
      match next (zip args pats ++ ms) $ subst evName (TConF tCName' inds (NoBnd ()) tytel) bod -- insert vacous evidence (TODO something more efficient)

    -- overly conservative
    -- C (DConF dcName' args (_, NoBnd _) _ _) (TConF _ _ (NoBnd _) _) | dcName' /= dcName -> pure No 
    C (DConF dcName' args (_, NoBnd _) _ _) _ | dcName' /= dcName -> pure No
    DConF dcName' args (_, NoBnd _) _ _ | dcName' /= dcName -> pure No
    _ -> pure Stuck -- TODO expo




matches' :: (Alpha b, Fresh f, Subst Exp b) =>
  Next f
  -> [Exp] -> [Bind [Pat] b] -> f (Either ([Exp], [Bind [Pat] b]) b) -- TODO should also retune evaluated scruts
matches' next scrutinees [] = pure $ Left (scrutinees, [])

  -- TODO inefficint since that scrutinee is recalculated every branch!
  -- TODO can simplify much more then currently
matches' next scrutinees ms@((bndbod):rest) = do
  (pats, bod) <- unbind bndbod
  if length pats /= length scrutinees
    then pure $ Left (scrutinees, ms)
    else do 
    ans <- match next (zip scrutinees pats) bod
    case ans of
      Yes e -> pure $ Right e
      No -> matches' next scrutinees rest
      Stuck -> pure $ Left (scrutinees, ms)



-- matches ::
--   HasCallStack => 
--   (Fresh m) => 
--   Next m -> [Exp] -> [Match] -> m (Either ([Exp], [Match]) Exp)
matches :: HasCallStack => 
  Fresh f =>
  Next f
  -> [Exp] -> [Match] -> f (Either ([Exp], [Bind [Pat] Term]) Term)
matches next scrutinees ms = matches' next scrutinees (unMatch <$> ms)


zipTConM :: 
  HasCallStack => 
  (Monad m) =>
  (Exp -> Integer -> EqEv -> Exp -> m Exp) -> (Term, Term) -> Maybe (m Term)
zipTConM f ((TConF tCNamel indl (NoBnd _) tell), (TConF tCNamer indr (NoBnd _) telr))
  | tCNamel == tCNamer = Just $ do
    inds <- zipTConM' f tell 0 indl indr
    pure $ TConF tCNamel inds (NoBnd ()) tell
zipTConM _ _ = Nothing

zipDConM :: 
  HasCallStack => 
  (Monad m) =>
  (Exp -> Integer -> EqEv -> Exp -> m Exp) -> 
  (Exp -> Integer -> EqEv -> Exp -> m Exp) -> (Term, Term) ->  Maybe (m Term)
zipDConM f fty ((DConF dCNamel argl (tCNamel, NoBnd indl) tell teltyl), (DConF dCNamer argr (tCNamer, NoBnd indr) telr teltyr))
  | dCNamel == dCNamer = Just $ do
    ind <- zipTConM' fty teltyl 0 indl indr
    arg <- zipTConM' f tell 0 argl argr
    pure $ DConF dCNamel arg (tCNamel, NoBnd ind) tell teltyl
zipDConM _ _ _ = Nothing


zipTConM' :: 
  HasCallStack => 
  (Monad m) =>
  (Exp -> Integer -> EqEv -> Exp -> m Exp) -> (Tel Exp Ty ()) -> Integer -> [Term] -> [Term] -> m [Term]
zipTConM' f (TelBnd ty bndBod) i (l:lrest) (r:rrest) = do
  otu <- f l i ty r
  rest <- zipTConM' f (substBind bndBod otu) (i+1) lrest rrest
  pure $ otu : rest
zipTConM' _ (NoBnd _) _ [] [] = pure []
zipTConM' _ _ _ _ _ = error "missmatch len"



zipTCon :: 
  HasCallStack => 
  (Exp -> Integer -> EqEv -> Exp -> Exp) -> (Term, Term) -> Maybe Term
zipTCon f ((TConF tCNamel indl (NoBnd _) tell), (TConF tCNamer indr (NoBnd _) telr))
  | tCNamel == tCNamer = Just $ TConF tCNamel (zipTCon' f tell 0 indl indr) (NoBnd ()) tell
zipTCon _ _ = Nothing




zipDCon :: 
  HasCallStack => 
  (Exp -> Integer -> EqEv -> Exp -> Exp) -> 
  (Exp -> Integer -> EqEv -> Exp -> Exp) -> (Term, Term) ->  Maybe Term
zipDCon f fty ((DConF dCNamel argl (tCNamel, NoBnd indl) tell teltyl), (DConF dCNamer argr (tCNamer, NoBnd indr) telr teltyr))
  | dCNamel == dCNamer = let
    ind =  (zipTCon' fty teltyl 0 indl indr)
    in Just $ DConF dCNamel (zipTCon' f tell 0 argl argr) (tCNamel, NoBnd ind) tell teltyl
zipDCon _ _ _ = Nothing


zipTCon' :: 
  HasCallStack => 
  (Exp -> Integer -> EqEv -> Exp -> Exp) -> (Tel Exp Ty ()) -> Integer -> [Term] -> [Term] -> [Term]
zipTCon' f (TelBnd ty bndBod) i (l:lrest) (r:rrest) = let
  otu = f l i ty r
  in otu : zipTCon' f (substBind bndBod otu) (i+1) lrest rrest
zipTCon' _ (NoBnd _) _ [] [] = []
zipTCon' _ _ _ _ _ = error "missmatch len"


e0 = zipTCon' (\ _ _ _ _ -> TyU) (TelBnd TyU $ u $ TelBnd TyU $ u $ NoBnd ()) 0 [TyU,TyU] [TyU,TyU]


data YesNoStuck a --b
  = Yes a
  | No
  | Stuck --b
  deriving (Show)


whnf :: Fresh m => Exp -> m Exp
whnf x =  norm (noNext{critN = whnf}) x

-- | weak head normal form with data lookup
whnfd :: (Fresh m, WithDynDefs m) => Exp -> m Exp
whnfd  e@(Ref refName) = do
  me' <- getDefn' refName
  case me' of
    Just e' -> norm (noNext{critN = whnfd}) $ e'
    Nothing -> pure e
whnfd x =  norm (noNext{critN = whnfd}) x

-- bacuase of stupid cyclic dependencies
safeWhnf' :: (Fresh m, WithDynDefs m, MonadState Integer m) => Exp -> m Exp
safeWhnf' e@(f `App` a) = do
  i <- get
  if i > 0 
  then do
    put (i-1)
    norm (noNext{critN = safeWhnf'}) e
  else
    pure e
safeWhnf' e@(Ref refName) = do
  -- logg "refName="
  -- logg refName
  
  i <- get
  
  -- logg "i="
  -- logg i
  if i > 0 
  then do
    put (i-1)
    me' <- getDefn' refName
    
    -- logg "me'="
    -- logg me'
    case me' of
      Just e' -> norm (noNext{critN = safeWhnf'}) $ e'
      Nothing -> pure e
  else
    pure e
safeWhnf' e = norm (noNext{critN = safeWhnf'}) e

-- safe b y only takeing some i number of applications
safeWhnf :: (Fresh m, WithDynDefs m) => Integer -> Exp -> m Exp
safeWhnf i e = do
  (e',_) <- runStateT (safeWhnf' e) i
  pure e'

isValue (TyU) = True
isValue (Fun _) = True
isValue (Pi _ _) = True
isValue (DConF _ arg _ _ _) = all isValue arg
isValue (TConF _ ind _ _) = all isValue ind
isValue (C _ (Pi _ _)) = True
isValue (C u t) = isValue u && isValue t
isValue (Same l _ (Pi _ _) r) = True
isValue (Same l _ tev r) = isValue l && isValue tev && isValue r -- TODO think about this.. shouldn't block?
isValue (Union l (Pi _ _) r) = True
isValue (Union l tev r) = isValue l && isValue tev && isValue r
-- isValue (V _) = True -- ...  could go either way
isValue _ = False


-- allM :: Applicative f => (a -> f Bool) -> [a] -> f Bool
-- allM [] = pure True

-- nextCbv :: (Fresh m, WithDynDefs m) => Next m
-- nextCbv = (noNext{critN = cbv, after = cbv})
-- agarly open refferences
-- TODO will cuase a bt of redundant work
cbv :: (Fresh m, WithDynDefs m) => Exp -> m Exp
cbv (f `App` a) = do
  f' <- cbv f
  if isValue f'
  then do
    a' <- cbv a
    if isValue a'
    then norm (noNext{critN = cbv}) $ f' `App` a'
    else pure $ f' `App` a'
  else pure $ f' `App` a
cbv (DConF dcName args tel telAn telTyAn) = do
  args' <- mapM cbv args
  pure $ DConF dcName args' tel telAn telTyAn
cbv (TConF dcName inds tel telTyAn) = do
  inds' <- mapM cbv inds
  pure $ TConF dcName inds' tel telTyAn
cbv e@(Ref refName) = do
  me' <- getDefn' refName
  case me' of
    Just e' -> cbv e'
    Nothing -> pure e
cbv e@(Case scrutinees branches unmatched) = do
  scrutinees' <- cbvs scrutinees
  if all isValue scrutinees'
  then do
    norm (noNext{critN = cbv}) $ Case scrutinees' branches unmatched
  else pure $ Case scrutinees' branches unmatched 
cbv e = norm (noNext{critN = cbv}) e -- use the defualt behavior over Same...

cbvs :: (Fresh m, WithDynDefs m) => [Exp] -> m [Exp]
cbvs [] = pure []
cbvs (h:ls) = do
  h' <- cbv h
  if isValue h'
  then do
    ls' <- cbvs ls
    pure $ h' : ls'
  else pure $ h' : ls



data RunTimeError 
  = EqErr Exp Info Exp Exp
  | UnMatchedPatErr [Exp] [Pat] (Maybe SourceRange)
      deriving (
  -- Show, 
  Generic, Typeable)
  -- just for debugging
instance Alpha RunTimeError
instance AlphaLShow RunTimeError
instance Show RunTimeError where
  show = lfullshow


cbvErrNext :: (Fresh m, WithDynDefs m, MonadError RunTimeError m) => Next m
cbvErrNext = Next {
  critN = cbvOrErr,
  assert =err,
  after=cbvOrErr,
  unmatched=cbvUnmatchedErr}

cbvUnmatchedErr ::  (Fresh m, WithDynDefs m, MonadError RunTimeError m) => 
 Exp -- orig expression (TODO probly remove this at some point)
  -> [Exp] -- scrutninees
  -> Maybe ([[Pat]], Maybe SourceRange) -- warning info
  -> m Exp
cbvUnmatchedErr _ scrutninees (Just (pats,sr)) = do
  ei <- matches' cbvErrNext scrutninees (fmap (\ (x, y) -> bind x y) $ zip pats [0..])  --akward
  -- this is of course way more subtle then it seems like it should be... what if the cell required for the match non-terminates? since this is call by value, 
  case ei of
    Right i -> throwError $ UnMatchedPatErr scrutninees (pats !! i) sr
    
    Left l -> error $ "dirty error, " ++ lfullshow l
  
cbvUnmatchedErr e scrutninees _ = error $ "inncorrect pattern compilation, " ++ lfullshow e

err :: (Fresh m, WithDynDefs m, MonadError RunTimeError m) => Exp -> Info -> Exp -> Exp -> m Exp
err l info ev r = do
  ev' <- cbvOrErr ev
  l' <- cbvOrErr l
  r' <- cbvOrErr r
  if sameCon l' r' == Just False 
  then throwError $ EqErr l' info ev' r'
  else pure $ Same l' info ev' r'

-- cbvOrErr :: (Fresh m, WithDynDefs m) => Exp -> m Exp
cbvOrErr :: (Fresh m, WithDynDefs m, MonadError RunTimeError m) => Exp -> m Exp
-- cbvOrErr (Same l info ev r) = err l info ev r
cbvOrErr (f `App` a) = do
  f' <- cbvOrErr f
  logg ""
  -- loggg "f = "
  -- loggg $ lfullshow f
  -- loggg "isValue f' = "
  -- loggg $ show $ isValue f'
  -- loggg $ lfullshow f'
  if isValue f'
  then do
    a' <- cbvOrErr a
    -- loggg $ "isValue a' = " ++ (show $ isValue a')
    -- loggg $ lfullshow a'
    -- logg ""
    if isValue a'
    then norm cbvErrNext $ f' `App` a'
    else pure $ f' `App` a'
  else pure $ f' `App` a
cbvOrErr (DConF dcName args tel telAn telTyAn) = do
  -- logg "cbvOrErr (DConF ..)"
  -- logg dcName
  args' <- mapM cbvOrErr args
  -- args' <- cbvOrErrs args
  pure $ DConF dcName args' tel telAn telTyAn
cbvOrErr (TConF dcName inds tel telTyAn) = do
  inds' <- mapM cbvOrErr inds
  -- inds' <- cbvOrErrs inds
  pure $ TConF dcName inds' tel telTyAn
cbvOrErr e@(Ref refName) = do
  me' <- getDefn' refName
  case me' of
    Just e' -> cbvOrErr e'
    Nothing -> pure e
cbvOrErr e@(Case scrutinees branches unmatched) = do
  scrutinees' <- cbvOrErrs scrutinees
  if all isValue scrutinees'
  then norm cbvErrNext $ Case scrutinees' branches unmatched
  else pure $ Case scrutinees' branches unmatched 
  
cbvOrErr (Blame why sameTy) = do
  sameTy' <- norm cbvErrNext sameTy -- preffer type errors to term errors
  why' <- norm cbvErrNext why 
  pure $ Blame why' sameTy'

cbvOrErr e = norm cbvErrNext e 


cbvOrErrs :: (Fresh f, WithDynDefs f, MonadError RunTimeError f) => [Exp] -> f [Exp]
cbvOrErrs [] = pure []
cbvOrErrs (h:ls) = do
  h' <- cbvOrErr h
  
  -- logg ""
  -- logg "isValue h'"
  -- loggg $ show $ isValue h'
  -- loggg $ lfullshow h'
  -- logg ""
  if isValue h'
  then do
    ls' <- cbvOrErrs ls
    pure $ h' : ls'
  else pure $ h' : ls


-- cbvOrErr (f `App` a) = do
--   f' <- cbv f
--   if isValue f'
--   then do
--     a' <- cbv a
--     if isValue a'
--     then norm (noNext{critN = cbv}) $ f' `App` a'
--     else pure $ f' `App` a'
--   else pure $ f' `App` a
-- cbv (DConF dcName args tel telAn telTyAn) = do
--   args' <- mapM cbv args
--   pure $ DConF dcName args' tel telAn telTyAn
-- cbv (TConF dcName inds tel telTyAn) = do
--   inds' <- mapM cbv inds
--   pure $ TConF dcName inds' tel telTyAn
-- cbv e@(Ref refName) = do
--   me' <- getDefn' refName
--   case me' of
--     Just e' -> cbv e'
--     Nothing -> pure e
-- cbv e@(Case scrutinees branches unmatched) = do
--   scrutinees' <- cbvs scrutinees
--   if all isValue scrutinees'
--   then norm (noNext{critN = cbv}) $ Case scrutinees' branches unmatched
--   else pure $ Case scrutinees' branches unmatched 
-- cbv e = pure e -- norm (noNext{critN = cbv}) e -- TODO pure e?



-- TODO move to AST?
isCon :: Exp -> Bool
isCon TyU = True
isCon (Pi _ _) = True
isCon (Fun _) = True
isCon (DConF _ _ _ _ _) = True 
isCon (TConF _ _ _ _) = True 
-- debuggin
-- isCon ITy = True 
-- isCon (I _) = True 
-- isCon STy = True 
-- isCon (S i) = True 
-- otherwise
isCon _ = False

-- is 

sameCon :: Exp -> Exp -> Maybe Bool
sameCon TyU TyU = Just True
sameCon (TConF s1 ind1 _ _) (TConF s2 ind2 _ _) | s1 == s2 -- && length ind1 == length ind2 
  = Just True
sameCon (DConF s1 _ _ _ _) (DConF s2 _ _ _ _) | s1 == s2 = Just True
sameCon (Fun _) (Fun _) = Just True
sameCon (Pi _ _) (Pi _ _) = Just True
-- debuggin
-- sameCon ITy ITy = Just True
-- sameCon (I i) (I i') = Just $ i == i'
-- sameCon STy STy = Just True
-- sameCon (S i) (S i') = Just $ i == i'
-- contrediction
sameCon e1 e2 | isCon e1 && isCon e2 = Just False
sameCon _ _ = Nothing 
