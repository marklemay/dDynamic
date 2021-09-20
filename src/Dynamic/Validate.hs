module Dynamic.Validate where

-- import GHC.Stack

-- import  Env
-- import  Dynamic.Ast
-- import  Dynamic.Norm
-- import  Dynamic.Err
-- -- import  Dynamic.Temp
-- -- import qualified Dynamic.Env as C --TODO clean
-- import Dynamic.Env
-- -- import Dynamic.Norm (whnf)

-- import Data.Map (Map)
-- import qualified Data.Map as Map

-- import Data.Set (Set)
-- import qualified Data.Set as Set

-- import Data.Monoid (Any (..))
-- import Data.Typeable (Typeable)
-- import GHC.Generics (Generic)
-- import Unbound.Generics.LocallyNameless
-- import Unbound.Generics.LocallyNameless.Internal.Fold (foldMapOf, toListOf)
-- import Control.Monad.Except
-- import Unbound.Generics.LocallyNameless.Unsafe (unsafeUnbind)

-- import UnboundHelper
-- import Control.Monad.Reader (ReaderT, MonadReader(ask))
-- import Helper
-- import AlphaShow
-- import Control.Applicative


-- validate (Fun bndbod an) under = do
--   (p, bod) <- unbind bndbod
--   validate bod under

-- validate (App f a an) under = do
--   validate f under
--   validate a under

-- validate (Pi aTy bndbod) under = do
--   validate aTy under
--   (p, bod) <- unbind bndbod
--   validate bod under


-- data Issue