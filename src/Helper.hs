{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
module Helper where

import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless.Unsafe (unsafeUnbind)
import GHC.Generics (Generic)
import Data.Typeable (Typeable)

import Data.Map (Map)
import qualified Data.Map as Map

import Data.Monoid (Any(..))
import Control.Applicative (Alternative(empty),  Applicative(..), (<$>))
import Unbound.Generics.LocallyNameless.Internal.Fold (foldMapOf, toListOf)
import Ast
import UnboundHelper

import Control.Monad.Except (throwError, MonadError)
import Control.Monad (MonadPlus(..))

allM :: (Traversable t, Monad m) => (a -> m Bool) -> t a -> m Bool
allM p ca = all (True ==) <$> mapM p ca


toExp :: Pat -> Exp
toExp (PVar x) = V x
toExp (Pat dCName args) = DCon dCName `apps` fmap toExp args
-- subterm instace, toExp, fromExp, then smart constructors can use that

-- | as neutral form
-- neutral form in the sense of term rewriteing, as in https://cs.stackexchange.com/questions/69434/intuitive-explanation-of-neutral-normal-form-in-lambda-calculus/69457#69457
asNeu :: Exp -> Maybe (Exp, [Exp])
asNeu (Pos _ e _) = asNeu e
asNeu (V x) = Just (V x, [])
asNeu (DCon dCName) = Just (DCon dCName, [])
asNeu (TCon tCName) = Just (TCon tCName, [])
asNeu (f `App` a) = do 
  (h, args) <- asNeu f
  pure (h,  args ++ [a])
asNeu _ = Nothing


-- some standard helper functions (TODO: should probly be in other places)
(-->) aTy bodTy = Pi aTy $ u bodTy -- does not associate correctly


lam :: Var -> Term -> Term
lam arg bod = Fun (bind (s2n "_", arg) bod) 

apps :: Exp -> [Term] -> Exp
apps h [] = h
apps h (a : rest) = apps (h `App` a) rest



-- TODO could check nesting
validPos (Pos start e end) | start > end = False
validPos (Pos _ e _) = validPos e
validPos (e ::: t) = validPos e && validPos t
validPos (Fun (unsafeUnbind -> ((s,a),bod))) = validPos bod
validPos (e `App` t) = validPos e && validPos t
 --TODO ann
-- validPos (Case s _ bs) = validPos s &&  all (\ (Match dCName (unsafeUnbind -> (p,bod))) -> validPos bod) bs -- TODO playing with unsafe fire
validPos (Pi aTy (unsafeUnbind -> (a,bod))) = validPos aTy && validPos bod
validPos (Case s _ bs) = error "case not done yet"
validPos x = True


validPos' s e (Pos start ex end) =  s <= start && start <= end && end <= e && validPos' start end ex
validPos' s e (ex ::: t) = validPos' s e ex && validPos' s e t -- TODO could further check that ex starts befor t
validPos' s e (Fun (unsafeUnbind -> ((_,a),bod))) = validPos' s e bod
validPos' s e (f `App` a) = validPos' s e f && validPos' s e a
--  --TODO ann
-- -- validPos (Case s _ bs) = validPos s &&  all (\ (Match dCName (unsafeUnbind -> (p,bod))) -> validPos bod) bs -- TODO playing with unsafe fire
validPos' s e (Pi aTy (unsafeUnbind -> (a,bod))) = validPos' s e aTy && validPos' s e bod
validPos' s e TyU = True
validPos' s e (V _) = True
validPos' s e (Case sc _ bs) = error "case not done yet"
validPos' s e x = error "case not done yet"

