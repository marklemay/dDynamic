
module Dynamic.Unification where

import Unbound.Generics.LocallyNameless
import Control.Monad

import UnboundHelper

import Dynamic.Ast
import Dynamic.Norm
import Dynamic.Env

type Prob = (Exp,Exp,Path)
type Assign = (Var,Exp,Path) -- TODO needs to not reassign, but also order matters
type Unsat = (Exp,Exp,Path) -- TODO needs prior assignments?

-- TODO should unification only happen over surface pattens?


fOUni' :: [Prob] -> Either Unsat ([Assign],[Prob])
fOUni' [] = Right ([], [])

fOUni' (b@(l, r, p):rest) | sameCon l r == Just False = Left b
-- fOUni' ((l, r, _):rest) | aeq l r = fOUni' rest

-- --bit of a hack
-- fOUni' (((C u _ botTy _ topTy), r, p):rest) | aeq botTy topTy = fOUni' ((u,r, p):rest) 
-- fOUni' ((l, (C u _ botTy _ topTy), p):rest) | aeq botTy topTy = fOUni' ((l,u, p):rest) 

-- --bit more of a hack
-- fOUni' ((Csym u _ _ (An (Just topTy)), r, p):rest) | aeq (tyInf u) (Just topTy) = fOUni' ((u,r, p):rest) 
-- fOUni' ((l, Csym u _ _ (An (Just topTy)), p):rest) | aeq (tyInf u) (Just topTy) = fOUni' ((l,u, p):rest) 


fOUni' ((V x _, r, path):rest) = do -- TODO only if notn already bound!
  let a = (x,r,path)
  let rest' = subst x r rest
  (asigns, probs) <- fOUni' rest'
  pure (a : asigns, probs)
fOUni' ((l,V x _, path):rest) = do -- TODO only if notn already bound!
  let a = (x,l,Sym path)
  let rest' = subst x l rest
  (asigns, probs) <- fOUni' rest'
  let probs' = subst x l probs -- little inefficient
  pure (a : asigns, probs')

fOUni' ((TConF tCNamel argsl (An (Just (NoBnd _))),
         TConF tCNamer argsr (An (Just (NoBnd _))), path):rest) 
         | tCNamel == tCNamer && length argsl == length argsr = do
  let neweqs = fmap (\(l, r, i) -> (l, r, InjTcon path i)) $ zip3 argsl argsr [0..] 
  fOUni' $ neweqs ++ rest

fOUni' ((DConF dCNamel argsl (An (Just (_, NoBnd _))),
         DConF dCNamer argsr (An (Just (_, NoBnd _))), path):rest) 
         | dCNamel == dCNamer && length argsl == length argsr = do
  let neweqs = fmap (\(l, r, i) -> (l, r, InjDcon path i)) $ zip3 argsl argsr [0..] 
  fOUni' $ neweqs ++ rest
fOUni' (e:rest) = do
  (asigns, probs) <- fOUni' rest
  pure (asigns, e:probs)

fOUni :: (Fresh m, WithDynDefs m) => [Prob] -> m (Either Unsat ([Assign],[Prob]))
fOUni ls = 
  case fOUni' ls of
    Left unsat -> pure $ Left unsat
    Right (a,[]) -> pure $ Right (a,[])
    Right (a,probs) -> do
      probs' <- forM probs $ \ (l,r,p) -> do
        l' <- normClean l
        r' <- normClean r
        pure $ (l', r', p)
      if probs' == probs
        then pure $ Right (a, probs)
        else do
          stupidvarmnae <- fOUni probs'
          case stupidvarmnae of
            Right (a', p) ->  pure $ Right (a ++ a', p)
            x ->  pure $ x