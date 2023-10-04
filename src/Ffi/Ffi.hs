{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}

module Ffi.Ffi where
import Foreign.C


import Data.Aeson -- (FromJSON, ToJSON, decode, encode)
-- import qualified Data.ByteString.Lazy.Char8 as BL

import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless.Ignore

import GHC.Generics (Generic, SourceStrictness (SourceStrict))
import Data.Typeable (Typeable)

import Data.Map (Map)
import qualified Data.Map as Map

import Data.Monoid (Any(..))
import Control.Applicative (Applicative(..), (<$>))
import Unbound.Generics.LocallyNameless.Internal.Fold (foldMapOf, toListOf)
import UnboundHelper
import AlphaShow

import Control.Monad.Except (catchError, MonadError(throwError), runExcept)
import Control.Monad (guard, forM_) -- TODO: need a version with string error
import qualified Data.Foldable
import Control.Monad.Reader

import System.IO

import Debug.Trace

import Prelude hiding((^^), exp, pi, pred)
import Parser
import ParserMonad hiding (ParseError)
import Env
import Ast
-- import StdLib
import Norm
import Ty


import SourcePos

import qualified Dynamic.Ast as C
import qualified Dynamic.Norm as C
import qualified Dynamic.Norm as Dynamic.Norm
import qualified Dynamic.Err as C
import qualified Dynamic.Elab as C
import qualified Dynamic.ElabModule as C
import qualified Dynamic.Env as C
import qualified Dynamic.Warning as C
import qualified Dynamic.Visitor as C
import qualified Dynamic.Helper as C
import qualified Dynamic.Erasure as C
import PreludeHelper (logg, loggg, dPrinter, dTrace)
import qualified AlphaShow as C
import qualified Dynamic.ElabBase as C
import ParserMonad (ParseError)
import Control.Monad.Writer
import Dynamic.Ast (Info(origL))
import Unbound.Generics.LocallyNameless.Ignore
import Data.List (intersperse, sortBy, sort)
import Data.Function (on)
import Dynamic.Warning (Warning, src)

num _ = 4
foreign export ccall num :: Int -> Int


astr _ = newCString  "hello"
foreign export ccall astr :: Int ->  IO CString


explode _ = error "whopssies"
foreign export ccall explode :: Int ->  Int


doublestr :: CString -> IO CString
doublestr cs = do s <- peekCString cs; newCString $ s ++ s
foreign export ccall doublestr :: CString ->  IO CString

webPath = "" 

loadString :: String -> Res
loadString s = 
  let sr = Just $ SourceRange (Just s) (SourcePos webPath 0 0) (endPos webPath s) in

  -- putStrLn $ show $ pmstd path s

  case parseModule webPath s of
    Left ls -> ParseError ls
    Right m@(ddefs,trmdefs) -> 
      -- loggg $ lfullshow  m
      let em = runExcept $ runFreshMT $ C.elabmodule (empTyEnv{dataCtx=ddefs,defCtx=trmdefs}) sr in

      case em of
        Left e -> TypeError e

        Right mod ->  

          let 
            mod' = runFreshM $ C.visitModule mod (C.visitFresh C.visitorCleanSameDef)

            (mod'', warnings) = runWriter $ runFreshMT $ C.visitModule mod' (C.visitFresh C.visitorWarnSame)
           in
          
          -- pure $ Ok mod'' 
            Warnings warnings



parseModule :: Path -> String -> Either ParseError Module
parseModule path s = prettyParse path s $ token modulep 


-- since everything is dumb: structured data -> (json) String -> CString -> js string


instance ToJSON SourcePos
instance ToJSON SourceRange
instance ToJSON ParseError
instance ToJSON C.Err

instance ToJSON Info
instance ToJSON Warning

-- this is string for now
instance ToJSON C.Exp where
  toJSON e = object [ "userView" .=  (show $ runFreshM $ C.erase e)] -- risks some var capture

instance ToJSON C.Pat where
  toJSON e = object [ "userView" .=  (show $ runFreshM $ C.erasePat e)] -- risks some var capture


-- instance ToJSON C.Pat
instance ToJSON a => ToJSON (Ignore a) where
     toJSON (I a) = toJSON a

instance ToJSON C.ObsAtom


data Res
  = ParseError ParseError
  | TypeError C.Err
  | Warnings [Warning] 
  deriving (Generic)

instance ToJSON Res




check :: CString -> IO CString
check cs = do 
  s <- peekCString cs
  newCString $ show $ encode $ loadString s
foreign export ccall check :: CString ->  IO CString


-- tups _ = (6,7)
-- foreign export ccall tups :: Int -> (Int,Int)



-- nums _ = [4]
-- foreign export ccall nums :: Int -> [Int]



-- https://gitlab.haskell.org/ghc/ghc-wasm-meta