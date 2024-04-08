{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}

module Ffi.Ffi where
import Foreign.C


import Data.Aeson -- (FromJSON, ToJSON, decode, encode)
import qualified Data.ByteString.Lazy.Char8 as BL

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
import ParserMonad
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

-- copied form https://github.com/hellwolf/haskell-examples someday a library should handle this

import           Foreign.C.String
import           Foreign.Marshal.Alloc
import           Foreign.Ptr
import GHC.Base (undefined)
import SourcePos (SourceRange(SourceRange))

foreign export ccall callocBuffer :: Int -> IO (Ptr a)
callocBuffer = callocBytes
foreign export ccall freeBuffer :: Ptr a -> IO ()
freeBuffer = free



-- ...







foreign export ccall num :: Int -> Int
num x = x

foreign export ccall numNum :: Int -> IO Int
numNum x = pure x


foreign export ccall astr :: Int ->  IO CString
astr _ = newCString  "hello"



doublestr :: CString -> IO CString
doublestr cs = do s <- peekCString cs; newCString $ s ++ s
foreign export ccall doublestr :: CString ->  IO CString



foreign export ccall e1 :: CString -> IO CString
e1 _ = newCString $ BL.unpack $ encode debugSR 

foreign export ccall loadStringJson :: CString -> IO CString
loadStringJson cs = do s <- peekCString cs; newCString $ BL.unpack $ encode $ loadString s -- TODO unpack better than show?


-- TODO test how bad stuff works

foreign export ccall explode :: Int ->  Int
explode _ = error "whopssies"


webPath = "" 

loadString :: String -> Res
loadString s = 
  let sr = Just $ SourceRange (Just s) (SourcePos webPath 0 0) (endPos webPath s) in

  -- putStrLn $ show $ pmstd path s

  case parseModule webPath s of
    Left ls -> parseError ls
    Right (m@(ddefs,trmdefs), examples) -> 
      -- loggg $ lfullshow  m
      let em = runExcept $ runFreshMT $ C.elabmodule (empTyEnv{dataCtx=ddefs,defCtx=trmdefs}) sr in

      case em of
        Left e -> typeErrorToRes e

        Right mod -> do
          let mod' = runFreshM $ C.visitModule mod (C.visitFresh C.visitorCleanSameDef)

          let (mod'', warnings) = runWriter $ runFreshMT $ C.visitModule mod' (C.visitFresh C.visitorWarnSame)
          
          infos <- forM examples $ \ (start,end, example) -> do
            let sr = SourceRange (Just s) start end
            let exp' = C.underModule example mod''
            
            mExp <- runExceptT $ runFreshMT $ C.runWithModuleMT (C.runWithSourceLocMT (C.elabInf' exp' (C.empElabInfo Dynamic.Norm.whnfd) ) sr ) mod
            case mExp of
              Right (e,cty) -> do
                -- Info ((show (runFreshM $ C.erase e)) ++  " : " ++ show (runFreshM $ C.erase cty))
                me' <- runExceptT $ runFreshMT $ C.runWithModuleMT (Dynamic.Norm.whnfd e) mod
                case me' of
                  Right e' -> pure $ Info ((show (runFreshM $ C.erase e')) ++  " : " ++ (show (runFreshM $ C.erase cty))  ) (fullChar src start) (fullChar src end)
                  _ -> pure $ Info "TODO" (fullChar src start) (fullChar src end)
              _ -> pure $ Info "TODO" (fullChar src start) (fullChar src end)

          toRes warnings infos



-- getRes :: SourceRange -> Either Err (Term, Term) -> Either Warning Info
-- getRes (SourceRange (Just src) start end) (Right (e,cty)) = Right $ Info ((show (runFreshM $ C.erase e)) ++  " : " ++ show (runFreshM $ C.erase cty)) (fullChar src start) (fullChar src end)
-- getRes _ 

--   SourceRange (Just src) start end -> WarningWrapper w (C.getMsg w) (fullChar src start) (fullChar src end)) ws ) toRes

parseModule :: Path -> String -> Either ParseError Env.OpenModule
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


data WarningWrapper = WarningWrapper {warn::Warning, msg::String, warningStart::Int, warningEnd::Int}
  deriving (Generic)

instance ToJSON WarningWrapper



data Info = Info {msg::String, warningStart::Int, warningEnd::Int}
  deriving (Generic)

instance ToJSON Info

data Res
  = ParseError 
    {err::ParseError, start::Int, end::Int} -- for dumb codemirror theneeds the literal exact start and end
  | TypeError 
  {typeError::C.Err , typeErrorStart::Int, typeErrorEnd::Int} 
  | Warnings [WarningWrapper] [Info]
  deriving (Generic)

instance ToJSON Res

parseError :: ParserMonad.ParseError -> Res
parseError (pe@(ParserMonad.ParseError _ (SourceRange (Just src) start end))) = Ffi.Ffi.ParseError pe (fullChar src start) (fullChar src end)


typeErrorToRes :: C.Err -> Res
typeErrorToRes (te@(C.Msg _ (Just (SourceRange (Just src) start end)))) = TypeError te (fullChar src start) (fullChar src end)


toRes :: [Warning] ->  [Info] -> Res
toRes ws infos = Warnings (map (\ w -> case C.getRange w of
  SourceRange (Just src) start end -> WarningWrapper w (C.getMsg w) (fullChar src start) (fullChar src end)) ws ) toRes


warningsToRes :: [Warning] -> Res
warningsToRes ws = Warnings (map (\ w -> case C.getRange w of
  SourceRange (Just src) start end -> WarningWrapper w (C.getMsg w) (fullChar src start) (fullChar src end)) ws ) []


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