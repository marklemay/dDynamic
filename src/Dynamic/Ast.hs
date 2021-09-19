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


type PathVar = Name Path

-- TODO this can be revised closer to normal form
data Path
  = PathV PathVar -- Bool -- direction
    (An (Exp, Exp))
  | Step Info Exp Bool -- direction
    Exp Exp
  | Refl 
   --Exp
  | Sym Path -- TODO can simplify this away
  | Trans Path Path -- TODO can simplify this away
  | InjTcon Path Integer
  | InjDcon Path Integer
  | Debug String
  deriving (
  -- Show, 
  Generic, Typeable)

endpoints :: Path -> Maybe (Exp, Exp)
endpoints (Step _ _ _ l r) = Just (l, r)
endpoints (Sym (endpoints-> Just (l, r))) = Just (r, l)
endpoints (Trans (endpoints-> Just (l, _)) (endpoints-> Just (_, r))) = Just (l, r)
endpoints (PathV _ (An mendpt)) = mendpt
-- endpoints p = error $ "not done yet, " ++ show p
endpoints _ = Nothing

instance Alpha Path

instance Subst Exp Path
instance Subst Path Path where
  -- isCoerceVar (PathV x True _ _) = Just $ --SubstCoerce x (Just _)
  -- isCoerceVar _     = Nothing
  isvar (PathV x _) = Just (SubstName x)
  isvar _     = Nothing


instance Eq Path where
  (==) = aeq


instance AlphaLShow Path
instance Show Path where
  show = lfullshow


rev (Step info w d l r) = Step info w (not d) r l
rev Refl = Refl
rev (Trans l r) = Trans (rev l) (rev r)
rev (Sym p) = p
rev (InjTcon p i) = InjTcon (rev p) i
rev (InjDcon p i) = InjDcon (rev p) i
rev (Debug s) = Debug s
rev p = Sym p
-- rev (PathV pv d l r) = PathV pv (not d) r l
-- rev (Step i d l r) = Step i (not d) r l
-- rev (Refl e) = Refl e

mapInjTcon :: Path -> Integer -> Path
mapInjTcon Refl _ = Refl
mapInjTcon (Step info (TConF tCNameW argW _) d (TConF tCNamel argl _) (TConF tCNamer argr _)) i 
  | tCNamel == tCNamer && tCNamel == tCNameW 
    && length argl == length argr && length argl == length argW 
    && fromIntegral i < length argl 
  = Step (obsmap (Index i) info) (argW !! fromIntegral i) d (argl !! fromIntegral i) (argr !! fromIntegral i)
  -- NOTE: obsmap (Index i) is unneeded as that will already havebeen tracked in argW
mapInjTcon (Sym p) i = Sym $ mapInjTcon p i 
mapInjTcon (Trans l r) i = Trans (mapInjTcon l i) (mapInjTcon r i)
mapInjTcon (Debug s) i = Debug $ s ++ "." ++ show i
mapInjTcon p i = InjTcon p i

mapInjDcon Refl _ = Refl
mapInjDcon (Step info (DConF dCNameW argW _) d (DConF dCNamel argl _ ) (DConF dCNamer argr _)) i 
  | dCNamel == dCNamer && dCNamel == dCNameW 
    && length argl == length argr && length argl == length argW 
    && fromIntegral i < length argl 
  = Step (obsmap (Index i) info) (argW !! fromIntegral i) d (argl !! fromIntegral i) (argr !! fromIntegral i)
-- mapInjDcon (Step info d (InjDcon dCNamel argl _) (InjDcon dCNamer argr _)) i = Step (obsmap (Index i) info) d
mapInjDcon (Sym p) i = Sym $ mapInjDcon p i 
mapInjDcon (Trans l r) i = Trans (mapInjDcon l i) (mapInjDcon r i)
mapInjDcon (Debug s) i = Debug $ s ++ "." ++ show i
mapInjDcon p i = InjTcon p i



-- TODO degenerate into list
data Obs = 
  Base -- probly has position information
  | AppW Exp Obs | Index Integer Obs
  | Aty Obs | Bty Exp Obs
  deriving (
  -- Show, 
  Generic, Typeable)

instance Alpha Obs
instance Subst Exp Obs
instance Subst Path Obs

instance AlphaLShow Obs
instance Show Obs where
  show = lfullshow


data Info = Info SourceRange Obs (Map String Exp) (Ignore Exp) (Ignore Exp) -- TODO remove some (most?) of these parameters, somthing is cuasing a self reference that atleast makes show dificult
  | Dummy
  deriving (
  -- Show, 
  Generic, Typeable)

instance Alpha Info
instance Subst Exp Info --TODO capture these!!
instance Subst Path Info

-- instance AlphaLShow Info
instance AlphaLShow Info where
  aShow i _ = pure (Set.empty, "Dummy") 

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


newtype Match = Match (Bind [Pat] ([(Var,Path,Exp)], Either Path Term)) 
--TODO [(Var,Path,Exp)] -> An [(Var,Path,Exp)] so not relevent for eq
--TODO explicit stuck syntax so, Either Path Term -> Term
  deriving (
  -- Show, 
  Generic, Typeable)

instance Alpha Match
instance Subst Exp Match
instance Subst Path Match

instance AlphaLShow Match
instance Show Match where
  show = lfullshow

-- TODO: abstract this like a telescope
data Pat 
  = Pat PathVar DCName [Pat] -- TODO move PathVar to the right so it matches the order of the expression
  | PVar Var
  -- TODO ppos?
  deriving (Generic, Typeable)

instance Alpha Pat
instance Subst Exp Pat -- vacous substitution
instance Subst Path Pat -- vacous substitution

instance AlphaLShow Pat
instance Show Pat where
  show = lfullshow

patToExp :: Pat -> Exp
patToExp (PVar x) = V x noAn
patToExp (Pat pv dcname arg) = Csym (DConF dcname (patToExp <$> arg) noAn) (PathV pv noAn) (bind (s2n "x") $ V (s2n "x") noAn) noAn


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
  | DConF DCName [Term] (An (TCName, Tel Exp Ty [Term])) 

  | Case [Term] (An (Tel Exp Ty Ty)) [Match] (Maybe SourceRange) (An Ty) 
  -- TODO do something better with the motive.  I don't think anything uses it?
  -- TODO require enough info for a non exhuastiveness pattern
  
  | TyU -- Type in type

  | Csym Term Path (Bind Var Ty) -- typed
     (An Ty)
     -- Ty Info Ty 
  -- calue form of the above
  | C Term Info Ty Ty Ty -- typedbottom untyped typedTop
    -- TODO better name?
    -- TODO Info -> Srcloc?

  | Same Exp Obs Exp

  | Tag String -- debugging tag
  deriving
    ( Generic,
      Typeable
    )

under (Csym u _ _ _) = Just u 
under (C u _ _ _ _) = Just u 
under _ = Nothing

instance Alpha Exp where
instance Subst Exp Exp where
  -- `isvar` identifies the variable case in your AST.
  isvar (V x _) = Just (SubstName x)
  isvar _     = Nothing
instance Subst Path Exp

instance Eq Exp where
  (==) = aeq

instance AlphaLShow Exp
instance Show Exp where
  -- show = lfullshow
  show (V x _) = show x
  show (Fun (unsafeUnbind -> ((selfName, argName), bod)) _) = "(Fun " ++ show selfName ++ " " ++ show argName ++ " " ++ show bod ++ ")"
  -- show (App f a _) = "(" ++ show f ++ " " ++ show a ++ ")"
  -- show (App f a _) = "(" ++ show f ++ " `App` " ++ show a ++ ")"
  show (App f a ann) = "(App " ++ show f ++ " " ++ show a ++ " _)"
  show (Pi aTy (unsafeUnbind -> (argName, bod)) ) = "(" ++ show argName ++ ":" ++ show aTy ++ ")->" ++ show bod
  -- show (TCon tCName args) = "(" ++ show tCName ++ " " ++ (concat $ show <$> args) ++ ")" 
  show (TConF tCName args (An (Just (NoBnd ())))) = "(TConF " ++ show tCName ++ " " ++ (concat $ show <$> args) ++ ")" 
  show (TConF tCName args ann) = "(TConF " ++ show tCName ++ " [" ++ (concat $ show <$> args) ++ "] $ " ++ show ann ++ ")" 
  -- show (DConF dCName args _) = "(DConF " ++ show dCName ++ " ...)" 
  -- show (DConF dCName args _) = "(DConF " ++ show dCName ++ " " ++ (concat $ show <$> args) ++ ")" 
  show (DConF dCName args an) = "(DConF " ++ show dCName ++ " " ++ (concat $ show <$> args) ++ " " ++ show an ++ ")" 
  show (Case _ _ _ _ _) = "(Case  ...)" 
  show TyU = "*" 
  -- show (C e _ _ _ t) = "(C " ++ show e ++ " _ _ _ " ++ show t ++ ")" 
  
  show (C e _ u _ t) = "(C " ++ show e ++ " _ " ++ show u ++ " _ " ++show t ++ ")" 
  show (Csym e _ _ _) = "(Csym " ++ show e ++ " _ _ _)" 
  show (Same l _ r) = "(Same " ++ show l ++ " _ " ++ show r ++ ")" 
  -- show (Same l info r) = "(Same " ++ show l ++ " " ++ show info ++ " " ++ show r ++ ")" 
  show (Tag s) = s
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
-- ccase x y z = Case x y z noAn 
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
tyInf :: Exp -> Maybe Exp
tyInf TyU = Just TyU
tyInf (Pi _ _) = Just TyU -- optimistic
tyInf (TConF _ _ (An (Just par))) = Just $ tellAsFun' par $ \ _ -> TyU --TODO got to change some of these hlint settings
tyInf (V _ (An mty)) = mty
tyInf (App f a (An mty)) = mty
tyInf (Fun _ (An (Just (aTy, bndbodTy)))) = Just $ Pi aTy bndbodTy
tyInf (Csym _ _ _ (An mty)) = mty
-- tyInf (Csym _ (endpoints -> Just (_,r)) bndty) = Just $ substBind bndty r
tyInf (C _ _ _ _ ty) = Just ty
tyInf (DConF _ _ (An (Just (tCName, par)))) = Just $ tellAsFun' par (tCon tCName)
tyInf (Case _ _ _ _ (An mty)) = mty
-- tyInf e = error $ "not doen yet, " ++ show e 
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

