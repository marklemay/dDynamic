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


module Dynamic.Ast where

import Control.Applicative (Applicative (..), (<$>))
import Control.Monad (guard)
import Data.List (find)

import Data.Map (Map)
import qualified Data.Map as Map

import Data.Set (Set)
import qualified Data.Set as Set

import Data.Monoid (Any (..))
import Data.Typeable (Typeable)
import GHC.Generics (Generic)
import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless.Internal.Fold (foldMapOf, toListOf)
import Unbound.Generics.LocallyNameless.Unsafe (unsafeUnbind)

import UnboundHelper
import AlphaShow

import SourcePos

type Term = Exp
type Ty = Exp
type EqEv = Exp

type Var = Name Term
type PathVar = Var

-- | type constructor names
type TCName = String
-- newtype TCName = TCName String
--   deriving (Generic, Typeable, Eq, Ord)
-- | data constructor names
type DCName =  String
-- newtype DCName = DCName String
--   deriving (Generic, Typeable, Eq, Ord)
-- instance AlphaLShow DCName
-- instance Show DCName where
--   show = lfullshow
-- instance Alpha DCName
-- instance Subst Exp DCName
-- instance AlphaLShow TCName
-- instance Show TCName where
--   show = lfullshow
-- instance Alpha TCName
-- instance Subst Exp TCName


type RefName = String


data ObsAtom
  = AppW Exp
  | Index Integer
  | Aty
  | Bty Exp
  deriving (Generic, Typeable)
instance AlphaLShow ObsAtom
instance Show ObsAtom where
  show = lfullshow
instance Alpha ObsAtom
instance Subst Exp ObsAtom

-- for some backwards compatiblity
type Obs = [ObsAtom]

data Info = Info {sr::Maybe SourceRange, obs::[ObsAtom]}-- also capture env?
  deriving (Generic, Typeable)

appInfo :: Exp -> Info -> Info
appInfo e inf@(Info{obs=obs'}) = inf{obs=obs'++[AppW e]} 
argInfo :: Info -> Info
argInfo inf@(Info{obs=obs'}) = inf{obs=obs'++[Aty]} 
bodInfo :: Exp -> Info -> Info
bodInfo e inf@(Info{obs=obs'}) = inf{obs=obs'++[Bty e]} 
dconInfo :: Integer -> Info -> Info
dconInfo i inf@(Info{obs=obs'}) = inf{obs=obs'++[Index i]}
tconInfo :: Integer -> Info -> Info
tconInfo i inf@(Info{obs=obs'}) = inf{obs=obs'++[Index i]}



instance AlphaLShow Info
instance Show Info where
  show = lfullshow
instance Alpha Info
instance Subst Exp Info


newtype Match = Match (Bind [Pat] Term) 
--TODO [(Var,Path,Exp)] -> An [(Var,Path,Exp)] so not relevent for eq
--TODO explicit stuck syntax so, Either Path Term -> Term
  deriving (
  -- Show, 
  Generic, Typeable)

instance Alpha Match
instance Subst Exp Match

instance AlphaLShow Match
instance Show Match where
  show = lfullshow

-- TODO: abstract this like a telescope?
data Pat 
  = Pat DCName [Pat] PathVar -- TCName
  | PVar Var
  -- TODO ppos? definitely in the surface lang
  deriving (Generic, Typeable)

instance Alpha Pat
instance Subst Exp Pat -- vacous substitution

instance AlphaLShow Pat
instance Show Pat where
  show = lfullshow

-- patToExp :: Pat -> Exp
-- patToExp (PVar x) = V x
-- patToExp (Pat dcname arg pv) = 
--   C (DConF dcname (patToExp <$> arg) noAn) (Unindexed $ singName pv)

data DataDef = DataDef (Tel Term Ty ()) (Map DCName (Tel Term Ty [Term])) deriving (
  -- Show, 
  Generic, Typeable)
  -- jusdt for debugging
instance Alpha DataDef
-- instance Subst Exp DataDef
instance AlphaLShow DataDef
instance Show DataDef where
  show = lfullshow


-- TODO rethink annotations
data Exp
  = V Var
  | Ref RefName 
  --Terms
  | Fun (Bind (Var {- self -}, Var {- arg -}) Term)
  | App Term Term

  -- Types
  | Pi Ty (Bind Var Ty)

  | TConF TCName [Term] (Tel Exp Ty ()) -- running tel
    (Tel Exp Ty ()) --full
  | DConF DCName [Term] (TCName, Tel Exp Ty [Term])  -- running tel
    (Tel Exp Ty ()) --full
    (Tel Exp Ty ()) --full tcon (TODO if possible removes)

  | Case [Term] [Match] (An [([Pat], SourceRange)])

  | TyU -- Type in type

  -- wierder stuff

  | C Term EqEv

  | Blame EqEv EqEv -- and why are the types the same?

  | Same Exp Info EqEv Exp
  | Union Exp EqEv Exp

--  manipulate evidence, TODO rename Tind to Tindex?
  | Tind Integer EqEv
  | Dind Integer EqEv

-- debugging tags
  -- | ITy
  -- | I Integer
  -- | STy
  -- | S String
  deriving
    ( Generic,
      Typeable
    )

instance Alpha Exp
instance Subst Exp Exp where
  -- `isvar` identifies the variable case in your AST.
  isvar (V x) = Just (SubstName x)
  isvar _     = Nothing


instance Eq Exp where
  (==) = aeq

instance AlphaLShow Exp
instance Show Exp where
  show = lfullshow
  -- show (V x _) = show x
  -- show (Fun (unsafeUnbind -> ((selfName, argName), bod)) _) = "(Fun " ++ show selfName ++ " " ++ show argName ++ " " ++ show bod ++ ")"
  -- -- show (App f a _) = "(" ++ show f ++ " " ++ show a ++ ")"
  -- -- show (App f a _) = "(" ++ show f ++ " `App` " ++ show a ++ ")"
  -- show (App f a ann) = "(App " ++ show f ++ " " ++ show a ++ " _)"
  -- show (Pi aTy (unsafeUnbind -> (argName, bod)) ) = "(" ++ show argName ++ ":" ++ show aTy ++ ")->" ++ show bod
  -- -- show (TCon tCName args) = "(" ++ show tCName ++ " " ++ (concat $ show <$> args) ++ ")" 
  -- show (TConF tCName args (An (Just (NoBnd ())))) = "(TConF " ++ show tCName ++ " " ++ (concat $ show <$> args) ++ ")" 
  -- -- show (TConF tCName args ann) = "(TConF " ++ show tCName ++ " [" ++ (concat $ show <$> args) ++ "] $ " ++ show ann ++ ")" 
  -- show (TConF tCName args _) = "(TConF " ++ show tCName ++ " [" ++ (concat $ show <$> args) ++ "] )" 
  -- -- show (DConF dCName args _) = "(DConF " ++ show dCName ++ " ...)" 
  -- show (DConF dCName args _) = "(DConF " ++ show dCName ++ " " ++ (concat $ show <$> args) ++ ")" 
  -- -- show (DConF dCName args an) = "(DConF " ++ show dCName ++ " " ++ (concat $ show <$> args) ++ " " ++ show an ++ ")" 
  -- show (Case _ _ _ _ _) = "(Case  ...)" 
  -- show TyU = "*" 
  -- -- show (C e _ _ _ t) = "(C " ++ show e ++ " _ _ _ " ++ show t ++ ")" 
  -- -- show (C e _ u _ t) = "(C " ++ show e ++ " _ " ++ show u ++ " _ " ++show t ++ ")" 
  
  -- show (Same l _ _ r) = "(Same " ++ show l ++ " _ _ " ++ show r ++ ")" 
  -- -- show (Same l info r) = "(Same " ++ show l ++ " " ++ show info ++ " " ++ show r ++ ")" 
  -- -- show (Tag s) = s
  -- -- show _ = "?"
  -- show e = lfullshow e



-- TODO: where should this live?
tellAsFun' :: (Alpha t) => Tel Term Ty t -> (t -> Ty)-> Ty
tellAsFun' (NoBnd a) f = f a
tellAsFun' (TelBnd aTy bndRest) f = 
  let (aName, rest) = unsafeUnbind bndRest
  in Pi aTy $ bind aName (tellAsFun' rest f)-- TODO I don't think casting is needed here?

tellAsFun :: (Alpha t, Fresh m) => Tel Term Ty t -> (t -> m Ty)-> m Ty
tellAsFun (NoBnd a) f = f a
tellAsFun (TelBnd aTy bndRest) f = do
  (aName, rest) <- unbind bndRest
  bodTy <- tellAsFun rest f
  pure $ Pi aTy $ bind aName bodTy -- TODO I don't think casting is needed here?

-- TODO could be more general
underBinder :: (Fresh m, Alpha b) => Bind [Var] Term -> (Term->b) -> m (Maybe b)
underBinder bnda f = do
  (p, a) <- unbind bnda
  let b = f a
  -- logg b
  pure $ if exists (`occursIn` b) p
    then Nothing
    else Just b
    
exists :: (t -> Bool) -> [t] -> Bool
exists p [] = False
exists p (h : t) | p h = True
exists p (_ : t) = exists p t

