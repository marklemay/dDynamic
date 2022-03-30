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
import Dynamic.Env
import Dynamic.Err
import Unbound.Generics.LocallyNameless.Bind


-- only cleam up the evidence of the outermost term
-- dumbNormEv  :: HasCallStack => (Fresh m) => Exp ->  m Exp
-- dumbNormEv (C tm ev) = do
--   ev' <- dumbNorm ev
--   case ev' of
--     TyU -> pure tm
--     TyU -> pure tm


-- dumbNorm :: HasCallStack => (Fresh m) => Exp ->  m Exp
-- dumbNorm (C tm ev) = do
--   tm' <- dumbNorm tm
--   ev' <- dumbNorm ev
--   case (tm',ev') of
--     (C tmu evu, _) -> do
--       evuev' <- dumbNorm $ Union evu TyU ev'
--       case evuev' 

-- dumbNorm x = pure x

-- normEv :: 
--   HasCallStack => 
--   (Fresh m) => 
--   Exp -> 
--   (Exp -> Info -> EqEv -> Exp -> m Exp) -> (Exp -> m Exp) -> (Exp -> m Exp) -> 
--   m Exp
-- normEv 

data Next m = Next {
  chkN :: (Exp -> Info -> EqEv -> Exp -> m Exp),
  critN :: (Exp -> m Exp),
  critEv :: (Exp -> m Exp),
  critApp :: (Exp -> m Exp),
  critCast :: (Exp -> m Exp),
  after :: (Exp -> m Exp)
  }

-- -- norm up to the outermost cast, where the evidence is normalized
-- -- will not consolidate casts, or eat vacuous casts
-- normCast ::
--   HasCallStack => 
--   (Fresh m) => 
--   Exp -> Next m ->
--   m Exp
-- normCast (f `App` a) next = do
--   f' <- normCast f next
--   case f' of
--     Fun bndbndbod -> do
--       ((funName, aName), bod) <- unbind bndbndbod
--       after next $ subst aName a bod
-- -- TConF,DConF
--     C tm (Pi arTy bndbodTy) -> do
--       -- (aName, bodTy) <- unbind bndbodTy
--       let ac = C a arTy
--       after next  $ C (tm `App` ac) $ substBind bndbodTy ac
--     Same l info (Pi arTy bndbodTy) r -> do
--       let ac = C a arTy
--       after next $ Same (l `App` ac) (appInfo ac info) (substBind bndbodTy ac) (r `App` ac) 
--     Union l (Pi arTy bndbodTy) r -> do
--       let ac = C a arTy
--       after next $ Union (l `App` ac) (substBind bndbodTy ac) (r `App` ac)
--     _ -> pure $ f' `App` a

-- -- eliminate data
-- normCast (C u eqEv) next = do
--   eqEv' <- critEv next eqEv
--   pure (C u eqEv')
-- normCast (Same l info eqEv r) next = do
--   eqEv' <- critEv next eqEv
--   pure (Same l info eqEv' r)
-- normCast (Union l eqEv r) next = do
--   eqEv' <- critEv next eqEv
--   pure (Union l eqEv' r)
-- normCast x _ = pure x


--TODo name
-- critEv next
normEqEvid ::
  HasCallStack => 
  (Fresh m) => 
  Next m ->
  Exp -> 
  m Exp
normEqEvid next (Union l eqEv r) = do
  eqEv' <- normEqEvid next eqEv
  l' <- normEqEvid next l
  r' <- normEqEvid next r
  case (l', eqEv', r') of
    (TyU,TyU,TyU) -> pure TyU
    (Pi la blBod , TyU, Pi ra brBod) -> do
      (lName, lbod) <-unbind blBod
      let rbod = substBind brBod (V lName)
      -- xx <- unbind2 blBod brBod
      pure $ Pi (Union la  TyU ra) $ bind lName (Union lbod TyU rbod)
    _ -> pure (Union l' eqEv' r')
normEqEvid next (Same l info eqEv r) = do
  eqEv' <- normEqEvid next eqEv
  l' <- normEqEvid next l -- TODo should proble guard these
  r' <- normEqEvid next r
  case (l', eqEv', r') of
    (TyU,TyU,TyU) -> pure TyU
    (Pi la blBod , TyU, Pi ra brBod) -> do
      (lName, lbod) <-unbind blBod
      let rbod = substBind brBod (V lName)
      -- xx <- unbind2 blBod brBod
      pure $ Pi (Same la (argInfo info) TyU ra) $ bind lName (Same lbod (bodInfo (V lName) info) TyU rbod)
    _ -> pure (Same l' info eqEv' r')
normEqEvid next (C u eqEv) = do
  eqEv' <- normEqEvid next eqEv
  case eqEv' of
    TyU -> normEqEvid next u 
    _ -> pure (C u eqEv')
-- normEqEvid next (f `App` a) = normApp f a next (normEqEvid next)
normEqEvid n x = normElim n (normEqEvid n) x

-- just run eliminators in critical positions, need to call consolodateCast first
norm ::
  HasCallStack => 
  (Fresh m) => 
  Next m ->
  (Exp -> m Exp) ->
  Exp -> 
  m Exp
-- normElim (C u eqEv) next after = do
norm next after (Same l info eqEv r) = do
  l' <- norm next consolodateCastM l
  r' <- norm next consolodateCastM r
  case zipDCon (\ l i ev r -> (Same l (dconInfo i info) ev r)) (\ l i ev r -> (Same l (tconInfo i info) ev r)) l' r' of
      Just x -> after $ C x eqEv
      _ -> pure (Same l' info eqEv r')
    



  
-- consolidate tyhe outermost cast (and in Assert + Union), if there is one  
consolodateCast ::
  HasCallStack => 
  Exp -> Exp
consolodateCast (C u@(consolodateCast -> u') eqEv) = 
  case u' of
    C u'' eqEv'' -> (C u'' $ Union eqEv'' TyU eqEv)
    _ -> (C u' eqEv)
consolodateCast (Same l@(consolodateCast -> l') info eqEv r@(consolodateCast -> r')) = -- TODO could prob be more efficient
  case (l', r') of
    (C l'' eqEv'', _) -> consolodateCast (Same l'' info (Union eqEv'' TyU eqEv) r')
    (_ , C r'' eqEv'') -> consolodateCast (Same l' info (Union eqEv  TyU eqEv'') r'')
    _ ->  (Same l' info eqEv r')
consolodateCast (Union l@(consolodateCast -> l') eqEv r@(consolodateCast -> r')) = 
  case (l', r') of
    (C l'' eqEv'', _) -> consolodateCast (Union l'' (Union eqEv'' TyU eqEv) r')
    (_ , C r'' eqEv'') -> consolodateCast (Union l' (Union eqEv  TyU eqEv'') r'')
    _ ->  (Union l' eqEv r')
consolodateCast x = x


consolodateCastM ::
  HasCallStack => 
  (Fresh m) => 
  Exp -> m Exp
consolodateCastM (C u eqEv) = do
  u' <- consolodateCastM u
  case u' of
    C u'' eqEv'' -> pure (C u'' $ Union eqEv'' TyU eqEv)
    _ -> pure (C u' eqEv)
consolodateCastM (Same l info eqEv r) = do
  l' <- consolodateCastM l
  r' <- consolodateCastM r
  case (l', r') of
    (C l'' eqEv'', _) -> consolodateCastM (Same l'' info (Union eqEv'' TyU eqEv) r')
    (_ , C r'' eqEv'') -> consolodateCastM (Same l' info (Union eqEv  TyU eqEv'') r'')
    _ -> pure (Same l' info eqEv r')
consolodateCastM (Union l eqEv r) = do
  l' <- consolodateCastM l
  r' <- consolodateCastM r
  case (l', r') of
    (C l'' eqEv'', _) -> consolodateCastM (Union l'' (Union eqEv'' TyU eqEv) r')
    (_ , C r'' eqEv'') -> consolodateCastM (Union l' (Union eqEv  TyU eqEv'') r'')
    _ -> pure (Union l' eqEv r')
consolodateCastM x = pure x


-- run eliminators in critical positions, consolodate casts. for collecting scrutinees
-- should erase ::* ?
normCast ::
  HasCallStack => 
  (Fresh m) => 
  Next m -> (Exp -> m Exp) ->
  Exp -> 
  m Exp
normCast n after (C u eqEv) = do
  u' <- normCast n undefined u -- pure?
  case u' of
    C u'' eqEv'' -> after (C u'' $ Union eqEv'' TyU eqEv)
    _ -> pure (C u' eqEv)
normCast n after (Same l info eqEv r) = do
  -- eqEv' <- normEqEvid next eqEv
  l' <- normCast n undefined l -- TODo should proble guard these
  r' <- normCast n undefined r
  case (l', r') of
    (C l'' eqEv'', _) -> normCast n undefined (Same l'' undefined (Union eqEv'' TyU eqEv) r')
    (_ , C r'' eqEv'') -> normCast n undefined (Same l' undefined (Union eqEv  TyU eqEv'') r'')
    
    _ -> case zipDCon (\ l i ev r -> (Same l (dconInfo i info) ev r)) (\ l i ev r -> (Same l (tconInfo i info) ev r)) l' r' of
      Just x -> after $ C x eqEv
      _ -> pure (Same l' info eqEv r')

normCast n after x = normElim n (normCast n after) x



-- normData ::

zipTCon :: 
  HasCallStack => 
  (Exp -> Integer -> EqEv -> Exp -> Exp) -> Term -> Term -> Maybe Term
zipTCon f (TConF tCNamel indl (NoBnd _) tell) (TConF tCNamer indr (NoBnd _) telr)
  | tCNamel == tCNamer = Just $ TConF tCNamel (zipTCon' f tell 0 indl indr) (NoBnd ()) tell
zipTCon _ _ _ = Nothing

-- zipDConCast :: 
--   HasCallStack => 
--   (Exp -> Integer -> EqEv -> Exp -> Exp) -> 
--   (Exp -> Integer -> EqEv -> Exp -> Exp) -> Term -> Term -> Maybe Term
-- zipDConCast = 

zipDCon :: 
  HasCallStack => 
  (Exp -> Integer -> EqEv -> Exp -> Exp) -> 
  (Exp -> Integer -> EqEv -> Exp -> Exp) -> Term -> Term -> Maybe Term
zipDCon f fty (DConF dCNamel argl (tCNamel, NoBnd indl) tell teltyl) (DConF dCNamer argr (tCNamer, NoBnd indr) telr teltyr)
  | dCNamel == dCNamer = let
    ind =  (zipTCon' fty teltyl 0 indl indr)
    in Just $ DConF tCNamel (zipTCon' f tell 0 argl argr) (tCNamel, NoBnd ind) tell teltyl
zipDCon _ _ _ _ = Nothing


zipTCon' :: 
  HasCallStack => 
  (Exp -> Integer -> EqEv -> Exp -> Exp) -> (Tel Exp Ty ()) -> Integer -> [Term] -> [Term] -> [Term]
zipTCon' f (TelBnd ty bndBod) i (l:lrest) (r:rrest) = let
  otu = f l i ty r
  in zipTCon' f (substBind bndBod otu) (i+1) lrest rrest
zipTCon' _ (NoBnd _) _ [] [] = []
zipTCon' _ _ _ _ _ = error "missmatch len"



match :: 
  HasCallStack => 
  (Fresh m) => 
  Next m -> [(Exp,Pat)] -> Exp -> m (YesNoStuck Exp)
match next []  bod = pure $ Yes bod
match next ((e, PVar x):ms) bod = do 
  match next ms $ subst x e bod
match next ((e, Pat dcName pats evName tCName): ms) bod = do
  e' <- normCast next undefined e
  case e' of 
    C (DConF _ _ (tCName', _) _ _) ev | tCName' /= tCName -> pure $ Yes $ Blame ev -- hard fail if rwong type head
    C (DConF dcName' args (_, NoBnd _) _ _) ev | length args == length pats && dcName' == dcName -> match next (zip args pats ++ ms) $ subst evName ev bod
    DConF dcName' args (tCName', NoBnd inds) _ tytel | length args == length pats && dcName' == dcName -> 
      match next (zip args pats ++ ms) $ subst evName (TConF tCName' inds (NoBnd ()) tytel) bod -- insert vacous evidence (TODO something more efficient)
    C (DConF dcName' args (_, NoBnd _) _ _) ev | dcName' /= dcName -> pure No
    DConF dcName' args (_, NoBnd _) _ _| dcName' /= dcName -> pure No
    C a ev | isCon a -> pure $ Yes $ Blame ev -- hard fail if it is headed with any different constructor
    _ -> pure Stuck -- TODO exposing the partial stuck state as a valid expression would allow for more definitional eqs, and possibly make the metatheory easier

asDataCast :: Exp -> Maybe (DCName, [Exp], TCName, EqEv)
asDataCast (C (DConF dCName args (tCName, NoBnd _) _ _) ev) = Just (dCName, args, tCName, ev)
asDataCast (DConF dCName args (tCName, NoBnd inds) _ ty) = Just (dCName, args, tCName, TConF tCName inds (NoBnd ()) ty)
asDataCast _ = Nothing


data YesNoStuck a --b
  = Yes a
  | No
  | Stuck --b
  deriving (Show)







isCon :: Exp -> Bool
isCon TyU = True
isCon (Pi _ _) = True
isCon (Fun _) = True
isCon (DConF _ _ _ _ _) = True 
isCon (TConF _ _ _ _) = True 
-- debuggin
isCon ITy = True 
isCon (I _) = True 
isCon STy = True 
isCon (S i) = True 
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
sameCon ITy ITy = Just True
sameCon (I i) (I i') = Just $ i == i'
sameCon STy STy = Just True
sameCon (S i) (S i') = Just $ i == i'
-- contrediction
sameCon e1 e2 | isCon e1 && isCon e2 = Just False
sameCon _ _ = Nothing 





-- junk









-- normApp ::
--   HasCallStack => 
--   (Fresh m) => 
--   Exp -> Exp -> Next m -> (Exp -> m Exp) ->
--   m Exp
-- -- normApp (f `App` a) _ = pure x 
-- normApp (C u eqEv) a next after = do
--   eqEv' <- normEqEvid next eqEv
--   case eqEv' of
--     (Pi arTy bndbodTy) -> do
--       let ac = C a arTy
--       put <- C <$> normApp u ac next after <*> pure (substBind bndbodTy ac)
--       after put
--     _ -> pure ((C u eqEv') `App` a)
-- normApp (Same l info eqEv r) a next after = do
--   eqEv' <- normEqEvid next eqEv
--   case eqEv' of
--     (Pi arTy bndbodTy) -> do
--       let ac = C a arTy
--       Same <$> normApp l ac next after <*> pure (appInfo ac info) <*> pure (substBind bndbodTy ac) <*> normApp r ac next after
--     _ -> pure ((Same l info eqEv' r) `App` a)
-- normApp (Union l eqEv r) a next after = do
--   eqEv' <- normEqEvid next eqEv
--   case eqEv' of
--     (Pi arTy bndbodTy) -> do
--       let ac = C a arTy
--       Union <$> normApp l ac next after <*> pure (substBind bndbodTy ac) <*> normApp r ac next after
--     _ -> pure ((Union l eqEv' r) `App` a)
-- -- TConF,DConF
-- normApp (f `App` a') a next after = do
--   e <- normApp f a' next pure -- incorrect
--   normApp e a next after
-- -- data
-- normApp x a _ after = pure (x `App` a)





-- unionTy :: Maybe EqEv -> Maybe EqEv -> Maybe EqEv 
-- unionTy Nothing l = l
-- unionTy r Nothing = r
-- unionTy (Just r) (Just l)  = Just $ Union l TyU r

-- -- norms :: 
-- --   HasCallStack => 
-- --   (Fresh m) => 
-- --   Exp -> 
-- --   (Exp -> Info -> EqEv -> Exp -> m Exp) -> (Exp -> m Exp) -> -- (Exp -> m Exp) -> 
-- --   m (Exp, Maybe EqEv)
-- -- norms (C tm ev) chkN critN = do
-- --   (tm', evu) <- norms tm chkN critN 
-- --   pure (tm', unionTy evu (Just ev))

-- -- norms x chkN critN  = do
-- --   x' <- norm x chkN critN 
-- --   case x' of
-- --     (C u t) -> pure (u, (Just t))
-- --     _ -> pure (x', Nothing)
-- -- -- norms x chkN critN  = pure (x, Nothing)

-- normu :: 
--   HasCallStack => 
--   (Fresh m) => 
--   Exp -> EqEv ->
--   (Exp -> Info -> EqEv -> Exp -> m Exp) -> (Exp -> m Exp) -> -- (Exp -> m Exp) -> 
--   m (Exp, EqEv)
-- normu (C tm evu ) ev chkN critN  = do
--   normu tm (Union evu TyU ev) chkN critN 
-- normu x ev chkN critN  = do
--   -- critN?
--   x' <- norm x chkN critN 
--   case x' of
--     (C u t) -> pure (u, Union t TyU ev)
--     _ -> pure (x', ev)
-- -- TConF,DConF


-- -- TODO  is not fully enforced 
-- -- norm :: 
-- --   HasCallStack => 
-- --   (Fresh m) => 
-- --   Exp -> 
-- --   (Exp -> Info -> EqEv -> Exp -> m Exp) -> (Exp -> m Exp) -> -- (Exp -> m Exp) -> 
-- --   m Exp 
-- -- norm (V x)  _  critN  = pure $ V x
-- -- --   -- TODO: safely evaluate the annotation?
-- -- -- -- norm (tm ::: ty) critN  = critN tm
-- -- norm (C tm ev) chkN critN = do
-- --   (tm' , ev') <- normu tm ev chkN critN
-- --   ev'' <- critN ev' 
-- --   case ev'' of
-- --     TyU -> pure tm'
-- --     _ -> pure $ C tm' ev''

-- -- norm (f `App` arg) chkN critN  = do
-- --   f' <- critN f
-- --   case f' of
-- --     Fun bndbndbod -> do
-- --       ((funName, aName), bod) <- unbind bndbndbod
-- --       critN $ subst aName arg bod
-- -- -- TConF,DConF
-- --     C tm (Pi arTy bndbodTy) -> do
-- --       -- (aName, bodTy) <- unbind bndbodTy
-- --       let ac = C arg arTy
-- --       critN $ C (tm `App` ac) $ substBind bndbodTy ac
-- --     Same l info (Pi arTy bndbodTy) r -> do
-- --       let ac = C arg arTy
-- --       critN $ Same (l `App` ac) (appInfo ac info) (substBind bndbodTy ac) (r `App` ac) 
-- --     Union l (Pi arTy bndbodTy) r -> do
-- --       let ac = C arg arTy
-- --       critN $ Union (l `App` ac) (substBind bndbodTy ac) (r `App` ac)
-- --     _ -> pure $ f' `App` arg

-- -- norm (Same l info eqEv r) chkN critN  = do
-- --   -- TODO this cuases some redundant computations, could be spread out for more efficency
-- --   -- TODO consider a normToCast? though it is possible GHC is smart enough to figure this out
-- --   eqEv' <- critN eqEv
-- --   l' <- critN l
-- --   r' <- critN r
-- --   chkN l' info eqEv' r'
-- -- -- norm (Union l eqEv r) chkN critN  = do
-- -- --   -- TODO this cuases some redundant computations, could be spread out for more efficency
-- -- --   -- TODO consider a normToCast? though it is possible GHC is smart enough to figure this out
-- -- --   eqEv' <- critN eqEv
-- -- --   l' <- critN l
-- -- --   r' <- critN r
-- -- --   case (l', r', eqEv') of
-- -- --     (C trn t, _ , _) -> critN $ Union trn (Union t TyU eqEv') r'
-- -- --     (_ , _ , C trn t) -> critN $ Union l' (Union eqEv' TyU t) r'
-- -- --     (TyU , TyU , TyU) -> pure TyU
-- -- --     (Pi la blBod , TyU, Pi ra brBod) -> do
-- -- --       la' <-  la
-- -- --       ra' <-  ra
-- -- --       (lName, lbod) <-unbind blBod
-- -- --       let rbod = substBind brBod (V lName)
-- -- --       lbod' <-  lbod
-- -- --       rbod' <-  rbod
-- -- --       -- xx <- unbind2 blBod brBod
-- -- --       pure $ Pi (Union la' TyU ra') $ bind lName (Union lbod' TyU rbod')
-- -- --     (_ , _, _) -> pure $ Union l' eqEv' r'
  

-- --   -- -- check here? or is that too frequent?
-- --   -- case (l', r', eqEv') of
-- --   --   (C trn t, _ , _) -> critN $ Same trn info (Union t TyU eqEv') r'
-- --   --   (_ , _ , C trn t) -> critN $ Same l' info (Union eqEv' TyU t) r'
-- --   --   (TyU , TyU , TyU) -> pure TyU
-- --   --   (Pi la blBod , TyU, Pi ra brBod) -> do
-- --   --     la' <-  la
-- --   --     ra' <-  ra
-- --   --     (lName, lbod) <-unbind blBod
-- --   --     let rbod = substBind brBod (V lName)
-- --   --     lbod' <-  lbod
-- --   --     rbod' <-  rbod
-- --   --     -- xx <- unbind2 blBod brBod
-- --   --     pure $ Pi (Same la' (argInfo info) TyU ra') $ bind lName (Same lbod' (bodInfo (V lName) info) TyU rbod')
-- --   --   (_ , _, _) -> pure $ Same l' info eqEv' r'
    
  

-- -- -- norm (DCon dCName) critN  = pure $ DCon dCName
-- -- -- norm (TCon tCName) critN  = pure $ TCon tCName
 
-- -- -- -- things are now a bit more complicated, and order matters
-- -- -- -- need to take it pattern by pattern for the most lazy behavior
-- -- -- -- may need to override this specifically to reconstitute CBV behavuor

-- -- -- norm (Case scrutinees ann branches) critN  = do
-- -- --   scrutinees' <- mapM critN scrutinees -- TODO could be tighter, only normalize the scruts that can be tested 
  
-- -- --   ans <- matches critN  scrutinees branches
-- -- --   case ans of
-- -- --     Right e -> critN e
-- -- --     Left (scrutinee', branches') -> 
-- -- --       Case scrutinee' ann <$> mapM (\ (Match bndBod) -> do (pat, bod) <- unbind bndBod; bod' <-  bod; pure $ Match $ bind pat bod') branches'

-- -- -- -- norm TyU _ critN  = pure TyU
-- -- norm _ _ _ = undefined 


-- -- -- just enough checking to keep going
-- -- minCheck (C trn t) info eqEv r chkN critN  = chkN trn info (Union t TyU eqEv) r
-- -- minCheck l info eqEv (C trn t) chkN critN  = chkN l info (Union eqEv TyU t) trn
-- -- minCheck TyU info TyU TyU chkN critN  = pure TyU
-- -- minCheck (Pi la blBod ) info TyU (Pi ra brBod) chkN critN  = do
-- --   la' <-  la
-- --   ra' <-  ra
-- --   (lName, lbod) <-unbind blBod
-- --   let rbod = substBind brBod (V lName)
-- --   lbod' <-  lbod
-- --   rbod' <-  rbod
-- --   -- xx <- unbind2 blBod brBod
-- --   pure $ Pi (Same la' (argInfo info) TyU ra') $ bind lName (Same lbod' (bodInfo (V lName) info) TyU rbod')

-- -- minCheck l info eqEv r chkN critN  = do
-- --   l' <-  l
-- --   r' <-  r
-- --   eqEv' <-  eqEv
-- --   pure $ Same l' info eqEv' r'
