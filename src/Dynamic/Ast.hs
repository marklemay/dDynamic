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


data Obs = 
  Base -- probly has position information
  | AppW Exp Obs | Index Int Obs
  | Aty Obs | Bty Exp Obs
  deriving (
  -- Show, 
  Generic, Typeable)

instance Alpha Obs
instance Subst Exp Obs

instance AlphaLShow Obs
instance Show Obs where
  show = lfullshow


data Info = Info SourceRange Obs (Map String Exp) (Ignore Exp) (Ignore Exp)
  deriving (
  -- Show, 
  Generic, Typeable)

instance Alpha Info
instance Subst Exp Info

instance AlphaLShow Info
instance Show Info where
  show = lfullshow

obsmap :: (Obs -> Obs) -> Info -> Info
obsmap f (Info sr obs ctx l r) = Info sr (f obs) ctx l r

initInfo :: SourceRange -> Exp -> Exp -> Info
initInfo src l r = let
  vars = varLs l ++ varLs r
  in Info src Base (Map.fromList $ fmap (\x -> (name2String x, V x noAn)) vars) (ignore l) (ignore r)

-- Maddness
varLs :: Exp -> [Var]
varLs = toListOf fv 
varSet :: Exp -> Set Var
varSet e = Set.fromList $ toListOf fv e


type Term = Exp

type Ty = Exp


type Var = Name Term

-- | type constructor names
type TCName = String

-- | data constructor names
type DCName = String

data Match = Match DCName (Bind [Var] Term) deriving (
  -- Show, 
  Generic, Typeable)

instance Alpha Match
instance Subst Exp Match

instance AlphaLShow Match
instance Show Match where
  show = lfullshow


data DataDef = DataDef (Tel Term Ty ()) (Map DCName (Tel Term Ty [Term])) deriving (
  Show, 
  Generic, Typeable)
  -- don't really need this fancy stuff
-- instance Alpha DataDef
-- instance Subst Exp DataDef
-- instance AlphaLShow DataDef
-- instance Show DataDef where
--   show = lfullshow



data Exp
  = V Var (An Ty)
  | --Terms
    Fun (Bind (Var {- self -}, Var {- arg -}) Term) 
      (An (Ty, Bind Var Ty))
  | App Term Term (An Ty)

  | -- Types
    Pi Ty (Bind Var Ty)

  -- | TCon TCName [Term] -- TODO depricate
  | TConF TCName [Term] (An (Tel Exp Ty ()))
  | DCon DCName [Term] (An (TCName, [Term]))--TODO KILL THIS SUPER DEAD
  | DConF DCName [Term] (An (TCName, Tel Exp Ty [Term])) 

  -- | Case Term (Bind (Var,[Var]) Ty) [Match] (An (TCName, Ty)) -- TODO TODO Motive is vestigal
  | Case Term (Bind (Var,[Var]) Ty) [Match] (An (TCName, Ty)) -- The motive seems needed to calulate the casts
  | TyU -- Type in type

  | C Term Ty Exp Ty -- type annotations here, so it would be, C trm from why to 

  | Same Exp Info Exp
  -- | Same Exp SourceRange Obs Exp
  deriving
    ( Generic,
      Typeable
    )


instance Alpha Exp where
instance Subst Exp Exp where
  -- `isvar` identifies the variable case in your AST.
  isvar (V x _) = Just (SubstName x)
  isvar _     = Nothing

instance AlphaLShow Exp
instance Show Exp where
  -- show = lfullshow
  show (V x _) = show x
  show (Fun (unsafeUnbind -> ((selfName, argName), bod)) _) = "(Fun " ++ show selfName ++ " " ++ show argName ++ " " ++ show bod ++ ")"
  -- show (App f a _) = "(" ++ show f ++ " " ++ show a ++ ")"
  show (App f a _) = "(" ++ show f ++ " `App` " ++ show a ++ ")"
  show (Pi aTy (unsafeUnbind -> (argName, bod)) ) = "(" ++ show argName ++ ":" ++ show aTy ++ ")->" ++ show bod
  -- show (TCon tCName args) = "(" ++ show tCName ++ " " ++ (concat $ show <$> args) ++ ")" 
  show (TConF tCName args (An (Just (NoBnd ())))) = "(TConF " ++ show tCName ++ " " ++ (concat $ show <$> args) ++ ")" 
  show (TConF tCName args ann) = "(TConF " ++ show tCName ++ " [" ++ (concat $ show <$> args) ++ "] " ++ show ann ++ ")" 
  show (DCon dCName args _) = "(DCon " ++ show dCName ++ " ...)" 
  -- show (DConF dCName args _) = "(DConF " ++ show dCName ++ " ...)" 
  -- show (DConF dCName args _) = "(DConF " ++ show dCName ++ " " ++ (concat $ show <$> args) ++ ")" 
  show (DConF dCName args an) = "(DConF " ++ show dCName ++ " " ++ (concat $ show <$> args) ++ " " ++ show an ++ ")" 
  show (Case _ _ _ _) = "(Case  ...)" 
  show TyU = "*" 
  show (C e _ _ t) = "(C " ++ show e ++ " _ " ++ show t ++ ")" 
  show (Same l info r) = "(Same " ++ show l ++ " " ++ show info ++ " " ++ show r ++ ")" 
  show _ = "?"


tCon tCName args = TConF tCName args (An (Just (NoBnd ())))

tConPat (TConF tCName args (An (Just (NoBnd ())))) = Just (tCName, args)
tConPat (TConF tCName args (An Nothing)) = Just (tCName, args)
tConPat _ = Nothing 

-- dcon (DConF dCName args (An (Just (NoBnd _)))) = Just (tCName, args)
-- dcon (DConF tCName args (An Nothing)) = Just (tCName, args)
-- dcon _ = Nothing 

v x = V x noAn 
fun x = Fun x noAn 
app x y = App x y noAn 
ccase x y z = Case x y z noAn 
same l r ll = error "init here" --Same l ll Base r

-- ... : V 0 :: V 1
-- case 0 -> Bool | 1 -> Bool | _ -> Nat

-- ... : Bool :: Bool

cast trm ty ll = 
  case tyInf trm of
    Just ty' -> C trm (same ty' ty ll) ty
    _ -> error $ "could not infer the underlieing type of " ++ show trm

-- TODO genericize an erasure function that romoves annotations


tySyntax TyU = True
tySyntax (Pi _ _) = True
tySyntax (tConPat -> Just _) = True
tySyntax _ = False

-- TODO: read ty
tyInf ::  Exp -> Maybe Exp
tyInf TyU = Just TyU
tyInf (Pi _ _) = Just TyU -- optimistic
-- tyInf (TCon _ _) = Just TyU -- optimistic
tyInf (TConF _ _ (An (Just par))) = Just $ tellAsFun' par $ \ _ -> TyU --TODO got to change some of these hlint settings
tyInf (V _ (An mty)) = mty
tyInf (App f a (An mty)) =  mty
tyInf (Fun _ (An (Just (aTy, bndbodTy)))) = Just $ Pi aTy bndbodTy
tyInf (C _ _ _ ty) = Just ty
tyInf (DCon _ _ (An (Just (tCName, par)))) = Just $ tCon tCName par
tyInf (DConF _ _ (An (Just (tCName, par)))) = Just $ tellAsFun' par (tCon tCName)
tyInf (Case _ _ _ (An (Just (_, ty)))) = Just ty
tyInf _ = Nothing



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


lkUp :: DCName -> [Match] -> Maybe (Bind [Var] Term)
lkUp _ [] = Nothing
lkUp dCName (Match dCName' out : _) | dCName == dCName' = Just out
lkUp dCName (_: rest) = lkUp dCName rest


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

