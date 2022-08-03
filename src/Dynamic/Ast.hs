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
import Control.Monad (guard, join)
import Data.List (find, intersperse)

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
import GHC.Stack
import Data.Tree (flatten)

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
instance Eq ObsAtom where
  (==) = aeq
instance Ord ObsAtom where
  compare = acompare

-- for some backwards compatiblity
type Obs = [ObsAtom]

data Info = Info {sr::Maybe SourceRange, obs::[ObsAtom],  captured::Map String Exp, origL::Ignore Exp, origR::Ignore Exp }-- also capture env?
  deriving (Generic, Typeable)

initInfo :: Maybe SourceRange -> Exp -> Exp -> Info
initInfo msrc l r = let
  vars = varLs l ++ varLs r
  in Info msrc [] (Map.fromList $ fmap (\x -> (name2String x, V x)) vars) (ignore l) (ignore r)

initSame :: Maybe SourceRange -> Exp -> EqEv -> Exp -> Exp
initSame msrc l ev r  = Same l (initInfo msrc l r) ev r

dummyInfo = Info Nothing [] Map.empty (ignore TyU) (ignore TyU)

-- Maddness
varLs :: Exp -> [Var]
varLs = toListOf fv 
varSet :: Exp -> Set Var
varSet e = Set.fromList $ toListOf fv e

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



instance AlphaLShow Info where
  aShow _ Info{sr=sr, obs=obs} = do
    (srv,srs) <- aShow 0 sr
    (obsv,obss) <-  aShow 0 obs
    pure (srv `Set.union` obsv, "Info{sr="++srs ++", obs="++ obss ++"}" )

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

unMatch :: Match -> Bind [Pat] Term
unMatch (Match x) = x

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

patSum :: Pat -> String
patSum (PVar _) = "_"
patSum (Pat dCName args _) = "(" ++ concat (intersperse " " ([dCName] ++ (patSum <$> args))) ++ ")"

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

  | Case [Term] [Match] (An ([[Pat]],Maybe SourceRange))

  | TyU -- Type in type

  -- wierder stuff

  | C Term EqEv

  | Blame EqEv -- incorrect type constructor
    EqEv -- and why are the types the same?

  | Same Exp Info EqEv Exp
  -- | Union Exp EqEv Exp  
  -- TODO instead represent this as `Union (Set Exp) EqEv` where set is never empty, and the singleton works like C
  | Union (Set Exp) EqEv

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

instance Ord Exp where
  compare = acompare

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

union :: Exp -> EqEv -> Exp -> Exp
union = undefined


-- this extractor boiler plate should also be generated
--TODO generalize set to traversable?
flattenUnions' :: Exp -> ([Exp], [EqEv])
flattenUnions' (C es t) = let
  (es', t') = flattenUnions' es
  in (es', t')
flattenUnions' (Union es t) = let
  (es', t') = unzip $ fmap flattenUnions' (Set.toList es)
  in (join es', join t')
flattenUnions' e = ([e], [])

flattenUnions :: Set Exp -> EqEv -> (Set Exp, EqEv)
flattenUnions se ev = let
  (se', t') = unzip $ fmap flattenUnions' (Set.toList se)
  in (Set.fromList $ join se', Union (Set.fromList $  ev : join t') TyU)

allTyu :: Set Exp -> Maybe ()
allTyu = undefined

allPi :: Set Exp -> Maybe [(Ty, Bind Var Ty)] 
allPi = undefined

allTCon :: 
  HasCallStack => 
  Set Term -> Maybe [(TCName, [Term], (Tel Exp Ty ()), (Tel Exp Ty ()))] 
allTCon = undefined

allZipTCon :: 
  HasCallStack => 
  ([Exp] -> Integer -> EqEv -> Exp) -> Set Term -> Maybe Term
allZipTCon f (allTCon-> Just ls@((tCNamel, indl, (NoBnd _), tell):rest))
  | all (\ (tCName, _, b, _)-> tCNamel==tCName && 0 == depth b) rest = 
    Just $ TConF tCNamel (zipTelCon' f tell 0 (fmap (\(_, ind, _, _)-> ind) ls)) (NoBnd ()) tell
allZipTCon _ _ = Nothing

allDCon :: 
  HasCallStack => 
  Set Term -> Maybe [(DCName, [Term], (TCName, Tel Exp Ty [Term]),  -- running tel
    (Tel Exp Ty ()), --full
    (Tel Exp Ty ()))] 
allDCon = undefined

allzipDCon :: 
  HasCallStack => 
  ([Exp] -> Integer -> EqEv -> Exp) -> 
  ([Exp] -> Integer -> EqEv -> Exp) -> Set Term ->  Maybe Term
allzipDCon f fty (allDCon-> Just ls@((dCNamel, argl, (tCNamel, NoBnd indl), tell, teltyl):rest))
  | all (\ (dCName, _, (_,b), _, _)-> dCNamel==dCName && 0 == depth b) rest =  let
    ind =  (zipTelCon' fty teltyl 0 (fmap (\(_,_, (_,b), _, _)-> ind) ls)) -- combind all teh type leve indexes
    in Just $ DConF dCNamel (zipTelCon' f tell 0 (fmap (\(_,arg, _, _, _)-> arg) ls)) (tCNamel, NoBnd ind) tell teltyl
allzipDCon _ _ _ = Nothing

zipTelCon' :: 
  HasCallStack => 
  (t Term -> Integer -> EqEv -> Exp) -> (Tel Exp Ty ()) -> Integer -> [t Term] -> [Term]
zipTelCon' f (TelBnd ty bndBod) i (h:rest) = let
  otu = f h i ty
  in otu : zipTelCon' f (substBind bndBod otu) (i+1) rest
zipTelCon' _ (NoBnd _) _ [] = []
zipTelCon' _ _ _ _  = error "missmatch len"



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

