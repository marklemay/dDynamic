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

module Dynamic.Unification where
import GHC.Stack

import Unbound.Generics.LocallyNameless
import Control.Monad
import Control.Monad.Except
import Data.Typeable (Typeable)
import GHC.Generics (Generic)

import Data.Map (Map)
import qualified Data.Map as Map

import Data.Set (Set)
import qualified Data.Set as Set


import UnboundHelper
import AlphaShow


import Dynamic.Ast
import Dynamic.Norm hiding (whnf)
import Dynamic.Env hiding (whnf)
import Dynamic.ElabBase
import Dynamic.Err 
import PreludeHelper


instance Alpha Equation
instance Subst Exp Equation
instance AlphaLShow Equation
instance Show Equation where
  show = lfullshow
instance Eq Equation where
  (==) = aeq

type Cast = EqEv

substWhy :: Var -> Term -> EqEv -> Equation -> Equation
substWhy subThis withThis becuse (Equation {left= left', right= right', sameTy= sameTy',why= why'})= 
  Equation {
    left= subst subThis withThis left', 
    right= subst subThis withThis right',
    sameTy= (subst subThis becuse sameTy'),
    why= Union (subst subThis becuse left') tyok
      $ Union why' tyok (subst subThis becuse right') }
      where
        tyok = (Union (subst subThis becuse sameTy') TyU sameTy') 

substWhy' :: Var -> Term -> EqEv -> (Term, Cast, EqEv) -> (Term, Cast, EqEv)
substWhy' subThis withThis becuse (left, cast, why)= 
  (subst subThis ac left, cast', Union why cast' (subst subThis becuse left))
      where
        cast' = subst subThis becuse cast
        ac = C withThis cast




substAddWhyProb :: Var -> Term -> Cast -> EqEv -> Prob -> Prob
substAddWhyProb subThis withThis cast becuse (Prob {
  flex=flex,
  active=active,
  Dynamic.Unification.assign=assign,
  stuck=stuck,
  unsat=unsat
  }) = Prob {
  flex= subThis `Set.delete` flex ,
  active= fmap (substWhy subThis ac becuse) active,
  Dynamic.Unification.assign=  Map.insert subThis (withThis, cast, becuse) $ Map.map (substWhy' subThis withThis becuse) assign,
  stuck= fmap (substWhy subThis ac becuse) stuck,
  unsat= fmap (substWhy subThis ac becuse) unsat
  }
  where
    ac = C withThis cast


data Prob = Prob {
  -- possibly the entire elab env?
  -- Flex vars
  flex :: Set Var,
  active :: [Equation],
  assign :: Map Var (Term, Cast
  , EqEv) ,
  stuck :: [Equation],
  unsat :: [Equation]
} deriving (Generic, Typeable)
instance Alpha Prob
instance Subst Exp Prob
instance AlphaLShow Prob where
  -- TODO get prec right
  aShow _ (Prob{
    flex=flex,
    active=active,
    Dynamic.Unification.assign=assign,
    stuck=stuck,
    unsat=unsat
    }) =  do
    (varsflex, strflex) <- aShow 0 flex
    (varsactive, stractive) <- aShow 0 active
    (varsassign, strassign) <- aShow 0 assign
    (varsstuck, strstuck) <- aShow 0 stuck
    (varsunsat, strunsat) <- aShow 0 unsat
    pure (varsflex`Set.union`varsactive `Set.union` varsassign`Set.union` varsstuck `Set.union` varsunsat, 
      "Prob {flex="++ strflex ++ ", active=" ++stractive ++ ", assign=" ++strassign ++ ", stuck=" ++strstuck ++ ", unsat=" ++strunsat ++"}")
  
-- instance Show Prob 
instance Show Prob where
  show = lfullshow

initProb :: Set Var -> [Equation] -> Prob
initProb flex eqs = Prob flex eqs Map.empty [] []

data Sol = Sol {
  
}
-- Unsat
-- ...

-- type ProbUnActive = ( Set Var,Map Var (Term, Ty, EqEv) , [(Term, Ty,Term,Ty)], [(Term, Ty,Term,Ty)])
-- -- just redicovered lenses?

-- focusActive :: Prob -> ([(Term, Ty,Term,Ty)], ProbUnActive)
-- focusActive = undefined 

-- unFocusActive :: ([(Term, Ty,Term,Ty)], ProbUnActive) -> Prob
-- unFocusActive = undefined 

isFlex :: Prob -> Var -> Bool
isFlex (Prob {flex= flex}) v = Set.member v flex

fOUni' :: HasCallStack => (Fresh m) => 
  ElabInfo m -> Prob -> m Prob
fOUni' elabInfo prob@(Prob {active = [], stuck= []}) = pure prob
fOUni' elabInfo prob@(Prob {unsat = _:_}) = pure prob

fOUni' elabInfo prob@(Prob {active = bad@( Equation {left =l,right =r}) : active', unsat = unsat'}) | sameCon l r == Just False = do
  -- loggg $ "unsat"
  pure $ prob {active = active', unsat = bad : unsat'}
  -- fOUni' elabInfo $ prob {active = active', unsat = bad : unsat'}
fOUni' elabInfo prob@(Prob {
  active = (Equation {left = V x,right =r, why=why, sameTy=sameTy}) : active'})
  | isFlex prob x && not ( x `occursIn` r) = do
  -- loggg $ "assign r"
  -- let rc = C r sameTy 
  fOUni' elabInfo $ substAddWhyProb x r sameTy why  $ prob {active= active'}

fOUni' elabInfo prob@(Prob {
  active = (Equation {left = l,right =V x, why=why, sameTy=sameTy}) : active'})
  | isFlex prob x && not ( x `occursIn` l) = do
  -- loggg $ ""
  -- loggg $ "assign l"
  -- loggg $ "prob=" ++ lfullshow prob
  -- loggg $ "(x, l, sameTy, why)=" ++ lfullshow (x, l, sameTy, why)
  -- let rc = C r sameTy 
  fOUni' elabInfo $ substAddWhyProb x l sameTy why $ prob {active= active'}

fOUni' elabInfo prob@(Prob {
  active = (Equation {left = C l p,right =r, why=why, sameTy=sameTy}) : active'}) = do
  -- loggg $ "C _"
  fOUni' elabInfo $ prob {active = (Equation {left = l,right =r, why=why, sameTy= Union p TyU sameTy}) : active'}
fOUni' elabInfo prob@(Prob {
  active = (Equation {left = l,right = C r p, why=why, sameTy=sameTy}) : active'}) = do
  -- loggg $ "_ C"
  fOUni' elabInfo $ prob {active = (Equation {left = l,right =r, why=why, sameTy= Union sameTy TyU p}) : active'}

--TODO these cases should be subsumed by erased aeq
fOUni' elabInfo prob@(Prob {
  active = (Equation {left = TyU,right = TyU}) : active'}) = do
  -- loggg $ "TyU TyU"
  fOUni' elabInfo $ prob {active = active'}
fOUni' elabInfo prob@(Prob {
  active = (Equation {left = V x,right = V x'}) : active'}) | x == x' = do
  -- loggg $ "x == x'"
  fOUni' elabInfo $ prob {active = active'}
  
fOUni' elabInfo prob@(Prob {
  active = (top@Equation {left = l@(TConF {}),right = r@(TConF {}), why =why}) : active', unsat= unsat}) = do
  -- loggg $ "TConF TConF"

  -- loggg $ "l=" ++ lfullshow l 
  -- loggg $ "r=" ++ lfullshow r
  -- loggg $ "why=" ++ lfullshow why
  case tConIndEqs why l r of
    Just ls -> fOUni' elabInfo $ prob{active =  ls++ active'}
    Nothing -> fOUni' elabInfo $ prob{active =  active', unsat= top:unsat}

fOUni' elabInfo prob@(Prob {
  active = (top@Equation {left = l@(DConF {}),right = r@(DConF {}), why =why}) : active', unsat= unsat}) = do
  -- loggg $ "DConF DConF"
  case dConIndEqs why l r of
    Just ls -> fOUni' elabInfo $ prob{active = ls++ active'}
    Nothing -> fOUni' elabInfo $ prob{active = active', unsat= top:unsat}

fOUni' elabInfo prob@(Prob {active = top : active', stuck= stuck}) = do
  -- loggg $ "delay"
  fOUni' elabInfo $ prob {active = active', stuck= stuck++[top]}

fOUni' elabInfo@(ElabInfo{whnf=whnf}) prob@(Prob {active = [], stuck= stuck}) = do

  -- loggg $ "stuck=" ++ lfullshow stuck
  stuck' <- forM stuck $ \ eq@Equation{left=l, right=r} -> do
    l' <- whnf l
    r' <- whnf r
    pure $ eq{left=l', right=r'}

  -- loggg $ "stuck'=" ++ lfullshow stuck'
  if stuck' == stuck -- quite inefficient
    then pure $ prob
    else fOUni' elabInfo $ prob {active = stuck', stuck= []}
  

-- fOUni elabInfo prob@(Prob {unsat = []}) = pure prob
-- fOUni elabInfo prob@(Prob {active = [], stuck = []}) = pure prob
-- fOUni elabInfo@(ElabInfo{Dynamic.Elab.whnf=whnf})  prob@(Prob {active = [], stuck = stuck}) = do
--   stuck

fOUni flex e elabInfo = fOUni' elabInfo $ initProb flex e

-- get the indicies
tConIndEqs :: 
  HasCallStack => 
  EqEv -> Term ->  Term -> Maybe [Equation]
tConIndEqs  becuase (TConF tCNamel indl (NoBnd _) tell) (TConF tCNamer indr (NoBnd _) telr)
  | tCNamel == tCNamer = Just $ (tConIndEqs' Tind becuase tell 0 indl indr) 
tConIndEqs _ _ _ = Nothing

dConIndEqs :: 
  HasCallStack => 
  EqEv -> Term ->  Term -> Maybe [Equation]
dConIndEqs  becuase (DConF dCNamel indl (tCNamel, NoBnd _) tell _) (DConF dCNamer indr (tCNamer, NoBnd _) telr _)
  | dCNamel == dCNamer && tCNamel == tCNamer = Just $ (tConIndEqs' Dind becuase tell 0 indl indr) 
dConIndEqs _ _ _ = Nothing


tConIndEqs' :: 
  HasCallStack => (Integer -> EqEv -> EqEv) -> EqEv -> (Tel Exp Ty ()) -> Integer -> [Term] -> [Term] -> [Equation]
tConIndEqs' f becuase (TelBnd ty bndBod) i (l:lrest) (r:rrest) = let
  evid = f i becuase
  in Equation {left=l,right=r, why = evid, sameTy=ty} : tConIndEqs' Tind becuase (substBind bndBod evid) (i+1) lrest rrest
tConIndEqs' _ _ (NoBnd _) _ [] [] = []
tConIndEqs' _ _ _ _ _ _ = error "missmatch len"




