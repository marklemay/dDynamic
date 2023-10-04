{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}

{-# LANGUAGE CPP, GeneralizedNewtypeDeriving,
             FlexibleInstances, MultiParamTypeClasses,
             StandaloneDeriving,
             UndecidableInstances
  #-}
  
module MonadTransformers where




import Data.Map (Map)
import qualified Data.Map as Map


import Unbound.Generics.LocallyNameless
import Control.Monad.Identity (runIdentity, Identity)
import Control.Monad.Trans (MonadTrans(lift))
import Control.Monad (guard, MonadPlus,ap)
import qualified Data.Functor.Classes as DataFunctorClasses


import Control.Applicative
import Control.Monad ()
import Control.Monad.Identity
import Control.Monad.Trans

import qualified Control.Monad.Cont.Class as CC
import qualified Control.Monad.Error.Class as EC
import qualified Control.Monad.State.Class as StC
import qualified Control.Monad.Reader.Class as RC
import qualified Control.Monad.Writer.Class as WC
import Data.Bifunctor (Bifunctor(bimap))
import Control.Monad.Except
import Control.Monad.State.Strict (State)
import Control.Monad.State (StateT)
import Control.Monad.State (runState)
import Control.Monad.State (StateT(runStateT))
--import Control.Monad.Logic


class (Monad m) => MonadDelay m where
  delay :: m a -> m a

  undelay :: m a -> m (Either (m a) a)



-- an Except without the monadPulus/alternative nonsense the overides those logic intances
newtype EitherT e m a =
    EitherT { unEitherT :: ExceptT e m a }

rununEither m = runExcept $ unEitherT m

rununEitherT :: EitherT e m a -> m (Either e a)
rununEitherT m = runExceptT $ unEitherT m

class (Monad m) => MonadEither e m where
  stickLeft :: e -> m a


instance (Monad m) => MonadEither e (EitherT e m) where
  stickLeft e = EitherT $ throwError e



instance  (Monad m) => Functor (EitherT e m) where
  fmap f dtma = do a <- dtma; pure $ f a


instance  (Monad m) => Applicative (EitherT e  m) where
  pure = return
  (<*>) = ap

instance  (Monad m) => Monad (EitherT e m) where
  return a = EitherT $ pure a

  dtma >>= f = EitherT $ (unEitherT dtma) >>= \a -> unEitherT $ f a

instance MonadTrans (EitherT e) where
  lift m =  EitherT $ lift m


instance Fresh m => Fresh (EitherT e m) where
  fresh = lift . fresh



instance MonadError e m => MonadError e (EitherT ee m) where
  throwError = lift . throwError
 
  catchError m h = EitherT $ error "TODO"
  -- https://github.com/lambdageek/unbound-generics/blob/master/src/Unbound/Generics/LocallyNameless/Fresh.hs#L95


-- MonadState
instance StC.MonadState s m => StC.MonadState s (EitherT e m) where
  get = lift StC.get
  put = lift . StC.put


-- all this nonsense

instance (Alternative m, Monad m) => Alternative (EitherT e m) where
  empty = lift empty

  l <|> r = EitherT $ ExceptT $ (runExceptT $ unEitherT l) <|> (runExceptT $ unEitherT r) 


instance MonadPlus m => MonadPlus (EitherT e m) where


-- instance Fresh m => Fresh (LogicT m) where
--   fresh = lift . fresh


-- instance (MonadLogic m, MonadPlus m) => MonadLogic (FreshMT m) where
--   -- use the underling State imple
--   msplit freshma = FreshMT $ fmap (fmap $ \(a,ma) -> (a, FreshMT ma))  $ msplit $ unFreshMT freshma
--   -- TODO: this messes with delay in some of the supported libs

--   -- use underlieing representation so computation can be delayed
--   ml `interleave` mr = FreshMT $ unFreshMT ml `interleave` unFreshMT mr

  --TODO : implement all of the ops since the library provides a more efficient implementation
