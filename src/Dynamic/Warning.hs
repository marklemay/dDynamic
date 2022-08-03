{-# LANGUAGE GeneralizedNewtypeDeriving #-}
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


module Dynamic.Warning where
import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless.Internal.Fold (foldMapOf, toListOf)
import Unbound.Generics.LocallyNameless.Unsafe (unsafeUnbind)

import Data.Map (Map)
import qualified Data.Map as Map

import Dynamic.Ast

import Unbound.Generics.LocallyNameless.Unsafe (unsafeUnbind)
import Control.Monad.Writer
import Control.Monad.Identity
import UnboundHelper
import SourcePos
import Dynamic.Eq
import PreludeHelper
import Dynamic.ElabBase
import Dynamic.Visitor
import GHC.Generics
import Data.Data
import AlphaShow
import Unbound.Generics.LocallyNameless.Ignore (Ignore(I))
import Dynamic.Env (runWithModuleMT)
import Control.Monad.Except (runExceptT)
import Control.Monad.State (runStateT)

data Warning 
  = EqWarning Exp -- left
    Info Exp -- evidence
    Exp --right
  | Unmatched [[Pat]] --non-empty
    (Maybe SourceRange)
    deriving (
  -- Show, 
  Generic, Typeable)
  -- just for debugging
instance Alpha Warning
instance AlphaLShow Warning
instance Show Warning where
  show = lfullshow
instance Eq Warning where
  (==) = aeq
instance Ord Warning where
  compare = acompare

consolidate :: [Warning] -> 
  (Map SourceRange (Ty,Ty, Map Obs (Exp,Exp)), Map SourceRange [[Pat]], [Warning])
consolidate [] = (Map.empty, Map.empty, [])
consolidate (EqWarning l (Info{sr=(Just sr), obs=obs, origL= (I origL), origR= (I origR)}) _ r : rest) = let
  (se, sw, noSource) = consolidate rest
  in 
  case Map.lookup sr se of
    Nothing -> (Map.insert sr (origL, origR, Map.fromList [(obs, (l, r))]) se, sw, noSource)
    Just (_, _, om) -> (Map.insert sr (origL, origR, Map.insert obs (l, r) om)  se, sw, noSource)
consolidate (Unmatched ps (Just sr) : rest) = let
  (se, sw, noSource) = consolidate rest
  in 
  (se, Map.insert sr ps sw, noSource)

consolidate (w : rest) = let
  (se, sw, noSource) = consolidate rest
  in (se, sw, w : noSource)






src :: Warning -> Maybe SourceRange
src (Unmatched _ mrs) = mrs
src (EqWarning _ (Info {sr=sr}) _ _) = sr


visitorWarnSame :: (MonadWriter [Warning] m, Fresh m) => VisitorM m  Exp
visitorWarnSame = visitorSelf {
  vSame = \_ finish -> finish $ \ l info ev r -> do

    -- tell [(l, r, info)]
    tell [EqWarning l info ev r]
    pure $ Same l info ev r
  ,
  vCase = \_ finish -> finish $ \ scruts branches unmatched -> do
    case unmatched of 
      An (Just (p@(_:_), sr)) -> tell [Unmatched p sr]
      _ -> pure ()
      
    pure $ Case scruts (fmap (\ (p,e)-> Match $ bind p e) branches) unmatched
}

-- visitorCleanSame :: (Fresh m) => VisitorM m  Exp
-- visitorCleanSame = visitorSelf {
--   vSame = \_ finish -> finish $ \ l info ev r -> do

--     -- loggg ""
--     -- loggg ""
--     -- loggg ""
--     -- loggg ""
--     -- logg "Clean "
--     -- -- logg "l="
--     -- -- logg l

--     -- -- logg "!!"

--     -- l' <- whnf l
--     -- r' <- whnf r
--     -- eq l' info ev r'
--     eq l info ev r
-- }

visitorCleanSameDef :: (Fresh m, WithDynDefs m) => VisitorM m Exp
visitorCleanSameDef = visitorSelf {
  -- TODO maybe just flatten?
--   vUnion = \_ finish -> finish $ \ l ty r -> do
--     (me, _) <- runStateT (runExceptT $ eqrefl l (Just ty) r) 100 -- the error thriwn should now be impossible, should be able to make this more efficent
--     case me of
--         Right e -> pure e
--         _ -> pure $ Union l ty r
-- ,
  vSame = \_ finish -> finish $ \ l info ev r -> do
    -- eqDef l info ev r
    undefined
}




-- visitorCleanSameDef2 :: (Fresh m, WithDynDefs m) => VisitorM m (Exp,[Exp]) -- the expression and it's endpoints... TODO could and should be more efficient
-- visitorCleanSameDef2 = visitorSelf {
--   vSame = \_ finish -> finish $ \ l info ev r -> do
--     eqDef l info ev r
-- }


-- eraseCast e = runIdentity $ runFreshMT $ visitFresh visitorSelf {
--   vC = \_ finish -> finish $ \ trm _ -> pure trm
-- } e

eraseCast' :: Fresh m => Term -> m Exp
eraseCast' e = visitFresh visitorSelf {
  vC = \ (C trm _) _ -> eraseCast' trm
} e

eraseCast :: Term -> Exp
eraseCast e = runIdentity $ runFreshMT $ eraseCast' e
-- runIdentity $ runFreshMT $ 

e0 = rfc TyU

e1 = rfc $ initSame Nothing TyU TyU TyU 

e2 = rfc $ initSame Nothing TyU (initSame Nothing TyU TyU TyU) TyU -- should clean evidence
e3 = rfc $ initSame Nothing (initSame Nothing TyU TyU TyU) TyU (initSame Nothing TyU TyU TyU) -- should clean branches
e4 = rfc $ initSame Nothing (initSame Nothing TyU TyU TyU) (initSame Nothing TyU TyU TyU) (initSame Nothing TyU TyU TyU) -- should clean branches + evidence
e5 = rfc $ initSame Nothing (initSame Nothing (V $ s2n "x") TyU TyU) (initSame Nothing TyU TyU TyU) (initSame Nothing TyU TyU TyU) -- should remove asserion if matching endpoints


e6 = rwf $ visitFresh visitorWarnSame $  initSame Nothing (initSame Nothing (initSame Nothing TyU TyU TyU) TyU TyU ) TyU (initSame Nothing (initSame Nothing TyU TyU TyU) TyU TyU )
e7 = rwf $ visitFresh visitorWarnSame $  initSame Nothing (initSame Nothing (initSame Nothing (V $s2n "x") TyU TyU) TyU TyU ) TyU (initSame Nothing (initSame Nothing TyU TyU TyU) TyU TyU )

-- e1 = rwf $ visitFresh visitorWarnSame $ efun
-- (visitFresh visitorCleanSameDef TyU) 

-- e2 = rwf $ visitFresh visitorWarnSame $ initSame Nothing TyU TyU TyU 

-- e3 = rwf $ visitFresh visitorWarnSame $ initSame Nothing TyU TyU (initSame Nothing (initSame Nothing TyU TyU TyU ) TyU TyU ) 

rfc e = runIdentity $ runFreshMT $ runWithModuleMT  (visitFresh visitorCleanSameDef e) (Module Map.empty (DefCtx Map.empty))

rwf :: Monoid w => FreshMT (WriterT w Identity) a -> (a, w)
rwf e = runIdentity $ runWriterT $ runFreshMT $ e