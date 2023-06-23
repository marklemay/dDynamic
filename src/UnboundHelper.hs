{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DeriveDataTypeable, DeriveGeneric, MultiParamTypeClasses, FlexibleContexts, FlexibleInstances, DeriveFunctor, RankNTypes, LambdaCase  #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# LANGUAGE DefaultSignatures
             , FlexibleContexts
             , FlexibleInstances
             , GADTs
             , MultiParamTypeClasses
             , ScopedTypeVariables
             , TypeOperators
 #-}

module UnboundHelper where

import Unbound.Generics.LocallyNameless
import GHC.Generics (Generic)
import Data.Typeable (Typeable)

import Data.Map (Map)
import qualified Data.Map as Map

import Data.Set (Set)
import qualified Data.Set as Set

import Data.Monoid (Any(..))
import Control.Applicative (Alternative(empty),  Applicative(..), (<$>))
import Unbound.Generics.LocallyNameless.Internal.Fold (foldMapOf, toListOf)
import Unbound.Generics.LocallyNameless.Unsafe (unsafeUnbind)
import Unbound.Generics.LocallyNameless.Bind 

import Control.Monad.Except (throwError, MonadError)
import Control.Monad (MonadPlus(..))

import Debug.Trace (trace)
import Data.List

import AlphaShow
import Unbound.Generics.LocallyNameless.Name
-- import UnboundShow

-- a little hacky?
instance Show a => (Show (FreshM a)) where
  show a = show $ runFreshM a

-- | An 'An' is optional information               
newtype An a = An (Maybe a)  deriving (Show, Generic, Typeable, Functor)

instance (Alpha a) => Alpha (An a) where
    -- override default behavior so that annotations are ignored
    -- when comparing for alpha-equivalence
    aeq' _ _ _ = True

instance (Subst e a) => Subst e (An a)
--TODO: theck that this doesn't mess up the occurs check too much

instance (AlphaLShow a) => AlphaLShow (An a)
-- instance (AlphaShow a) => AlphaShow (An a)

noAn = An Nothing
ann x = An $ Just x

-- see https://github.com/sweirich/pi-forall/blob/2014/notes4.md#specifying-the-type-system-with-basic-datatypes
data Tel n a b = NoBnd b
    | TelBnd a (Bind (Name n) (Tel n a b))
  deriving (Show, Generic, Typeable)

-- for testing
instance (Typeable n, Alpha a, Alpha b) => Eq (Tel n a b) where
  (==) = aeq

instance (Typeable n, Alpha a, Alpha b) => Alpha (Tel n a b)
instance (Typeable n, Alpha a, Alpha b, Subst e a, Subst e b) => Subst e (Tel n a b)

instance (Typeable n, AlphaLShow a, AlphaLShow b) => AlphaLShow (Tel n a b)

unbinds :: (Typeable n, Alpha a, Alpha b) => (Fresh m) => Tel n a b -> m ([(Name n,a)],b)
unbinds (NoBnd b) = pure ([], b)
unbinds (TelBnd a bndRest) = do
  (x, rest) <- unbind bndRest
  (ls, b) <- unbinds rest
  pure $ ((x,a):ls, b)

-- a little unsafe
tmap f (NoBnd b) = NoBnd $ f b
tmap f (TelBnd a bndbod) = do
  (v, bod) <- unbind bndbod
  TelBnd a . bind v <$> tmap f bod


tmapM af bf (NoBnd b) = do
  b' <- bf b
  pure $ NoBnd b'
tmapM af bf (TelBnd a bndbod) = do
  a' <- af a
  (v, bod) <- unbind bndbod
  bod' <- tmapM af bf bod
  pure $ TelBnd a' $ bind v bod'

unsafeTelMap f (NoBnd b) = NoBnd $ f b
unsafeTelMap f (TelBnd a (B p bod)) = TelBnd a (B p $ unsafeTelMap f bod)

substBindTel (NoBnd a) [] = ([], a)
substBindTel (TelBnd ty bndRestTel) (arg:rest) = let
  restTel = substBind bndRestTel arg
  (tys, a) = substBindTel restTel rest
  in (ty:tys, a)


depth :: (Typeable n, Alpha a, Alpha b) => Tel n a b -> Integer
depth (NoBnd _) = 0
depth (TelBnd _ bndtel) = 1 + (depth $ snd $ unsafeUnbind bndtel)



-- TODO : has this not already been done?
instance (Alpha a, Ord a) => Alpha (Set a) where
  aeq' actx l r = let
    l' = sortBy acompare $ Set.toList l
    r' = sortBy acompare $ Set.toList r
    in aeq' actx l' r' -- TODO possible wierdness with repeated aeq elements 
  fvAny' actx nfn sa =  let -- TODO almost definitely better way to do this
    flsa = fvAny' actx nfn $ Set.toList sa
    in fmap Set.fromList flsa
  close actx npath = Set.map (close actx npath)
  open actx npath =  Set.map (open actx npath)
  isPat   =  error "not yet implemented"  
  isTerm    =  error "not yet implemented"  
  isEmbed     =  error "not yet implemented"  
  nthPatFind      =  error "not yet implemented"  
  namePatFind       =  error "not yet implemented"  
  swaps'       =  error "not yet implemented"  
  lfreshen'       =  error "not yet implemented"  
  acompare' =  error "not yet implemented"  
  freshen' =  error "not yet implemented"  
  has' =  error "not yet implemented"  

instance (Subst b a, Ord a) => Subst b (Set a) where
  subst replaceThis withThis = Set.map (subst replaceThis withThis)
  substs subs = Set.map (substs subs)
  substBvs ctx withThese = Set.map (substBvs ctx withThese)

instance (Ord a, AlphaLShow a) => AlphaLShow (Set a) where
  aShow _ m = do
    mid <- mapM (aShow 0) $ Set.toList m
    pure (Set.unions (fmap fst mid), "fromList [" ++ concat (intersperse "," (fmap snd mid)) ++ "]")

-- TODO standard?
tyBreak :: Ordering -> Ordering -> Ordering
tyBreak EQ x = x
tyBreak x _ = x

-- only operate over values or there is a risk of subtle key colision
instance (Alpha v, Ord k, Show k) => Alpha (Map k v) where
  aeq' actx l r = 
    let
    l' = sortBy (\ (k, v) (k', v') -> (v `acompare` v') `tyBreak` (k `compare` k')) $ Map.toList l -- TODO pretty inefficient
    r' = sortBy (\ (k, v) (k', v') -> (v `acompare` v') `tyBreak` (k `compare` k')) $ Map.toList r
    in (fst <$> l') == (fst <$> r') && aeq' actx (snd <$> l') (snd <$> r') 
  fvAny' actx nfn sa = 
    let -- TODO almost definitely better way to do this
    masList =  Map.toList sa
    flsa = fvAny' actx nfn $ fmap snd masList
    in fmap (\ x -> Map.fromList $ zip (fmap fst masList) x) flsa

    -- let -- TODO almost definitely better way to do this
    -- masList = Map.toList sa
    -- flsa = fvAny' actx nfn $ fmap snd masList
    -- in fmap Map.fromList $ _ -- zip (fst masList) flsa
  close actx npath = Map.map (close actx npath)
  open actx npath = Map.map (open actx npath)
  isPat   =  error "not yet implemented"  
  isTerm    =  error "not yet implemented"  
  isEmbed     =  error "not yet implemented"  
  nthPatFind      =  error "not yet implemented"  
  namePatFind       =  error "not yet implemented"  
  swaps'       =  error "not yet implemented"  
  lfreshen'       =  error "not yet implemented"  
  acompare' =  error "not yet implemented"  
  freshen' =  error "not yet implemented"   
  has' =  error "not yet implemented"  


instance (Subst b v, Ord k, Show k) => Subst b (Map k v) where
  subst replaceThise withThis = Map.map (subst replaceThise withThis)
  substs subs = Map.map (substs subs)
  substBvs ctx withThese = Map.map (substBvs ctx withThese)

instance (AlphaLShow k, Ord k, AlphaLShow v) => AlphaLShow (Map k v) where
  aShow _ m = do
    mid <- mapM (aShow 0) $ Map.toList m
    pure (Set.unions (fmap fst mid), "fromList [" ++ concat (intersperse "," (fmap snd mid)) ++ "]")

--  lfullshow $ Map.fromList [("hi", V (s2n "x"))]

-- TODO a type to capure substitutions
-- data Cap a = Cap a deriving (Show)

unnamed = s2n "_"
u t = bind unnamed t -- TODO generalize over all patterns

-- TODO depricate in favor of forked unbound generics that suports look up of bound vars
-- from https://github.com/lambdageek/unbound-generics/blob/040ca46c404e1a2d02d2e22c9b3038f29282a757/test/PropOpenClose.hs
occursIn :: (Typeable a, Alpha b) => Name a -> b -> Bool
occursIn = elementOf fv
  where
    elementOf l = anyOf l . (==)
    anyOf l f = getAny . foldMapOf l (Any . f)

substsBind' :: (Subst a b, Typeable a, Alpha b, Fresh m) => Bind [Name a] b -> [a] -> m b
substsBind' bndb a = do
  (x , b) <- unbind bndb
  pure $ substs (zip x a) b

substssBind' :: (Subst a b, Typeable a, Alpha b, Fresh m) => Bind ([Name a], Name a) b -> ([a], a)-> m b
substssBind' bndb (as,a) =  do
  ((xs,x) , b) <- unbind bndb
  pure $ substs (zip xs as) $ subst x a b

-- allow for the same underlieng name qithout need ing to worry aboutindicies and such
rename :: Name a -> Name b
rename (Fn s i) = (Fn s i)
rename (Bn j i) = (Bn j i)