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
{-# LANGUAGE DoAndIfThenElse #-}

module Repl where

import Unbound.Generics.LocallyNameless
import GHC.Generics (Generic, SourceStrictness (SourceStrict))
import Data.Typeable (Typeable)

import Data.Map (Map)
import qualified Data.Map as Map

import Data.Monoid (Any(..))
import Control.Applicative (Applicative(..), (<$>))
import Unbound.Generics.LocallyNameless.Internal.Fold (foldMapOf, toListOf)
import UnboundHelper
import AlphaShow

import Control.Monad.Except (catchError, MonadError(throwError), runExceptT)
import Control.Monad (guard) -- TODO: need a version with string error
import qualified Data.Foldable
import Control.Monad.Reader

-- for command line features
import System.Console.Haskeline

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


-- TOOD cmds: clean, whnf, :r

-- runFile :: FilePath -> IO LangOut
-- runFile path = 
--   do program <- readFile path
--      return $ exec program



loadFile path = do
  s <- readFile path
  let sr = Just $ SourceRange (Just s) (SourcePos path 0 0) (endPos path s)
  putStrLn s
  putStrLn ""
  -- putStrLn $ show $ pmstd path s

  case parseModule path s of
    Left ls -> pure $ ParseError ls
    Right m@(ddefs,trmdefs) -> do
      putStrLn "parsed"
      -- loggg $ lfullshow  m
      em <- runExceptT $ runFreshMT $ C.elabmodule (empTyEnv{dataCtx=ddefs,defCtx=trmdefs}) sr 

      case em of
        Left e -> do 
          putStrLn ""
          putStrLn ""
          putStrLn $ C.prettyErr e
          putStrLn ""
          putStrLn ""
          putStrLn ""

          pure $ TypeError e

        Right mod -> do 

          -- putStrLn $ lfullshow mod
          putStrLn "elaborated" -- TODO after this point the programmer no longer needs to be blocked, 

          -- loggg $ lfullshow mod
          mod' <- runFreshMT $ C.visitModule mod (C.visitFresh C.visitorCleanSameDef)
          putStrLn "cleaned"

          -- loggg $ lfullshow mod'
          (mod'', warnings) <- runWriterT $ runFreshMT $ C.visitModule mod' (C.visitFresh C.visitorWarnSame)
          
          if null warnings
          then pure ()
          else putStrLn "warnings:"


          forM_ (sortBy (compare `on` src) warnings) $ \ w -> do
            -- putStrLn ""
            case w of
              C.EqWarning l info@C.Info{C.sr=msr,C.origL=I origL,C.origR=I origR} _ r -> do
                putStrLn "possibly mismatched types: "
                case msr of
                  Just src -> putStrLn $ unlines $ ("  " ++) <$> prettyRange src
                  Nothing -> pure ()
                
                l' <- runFreshMT $ C.erase l
                r' <- runFreshMT $ C.erase r

                origL' <- runFreshMT $ C.erase origL
                origR' <- runFreshMT $ C.erase origR

                if (show origL', show origR') /= (show l', show r') 
                then putStrLn $ "  " ++ show origL' ++ " =?= " ++ show origR' ++ " ~>"
                else pure ()
                putStrLn $ "  " ++ show l' ++ " =?= " ++ show r'
                -- loggg $ lfullshow w
                putStrLn ""
              C.Unmatched ps msr -> do
                putStrLn "possibly unmatched patterns: "

                case msr of
                  Just src -> putStrLn $ unlines $ ("  " ++) <$>  prettyRange src
                  Nothing -> pure ()
                
                forM_ ps $ \ p ->
                  -- TODO could do some fancy padding here
                  putStrLn $ "  | " ++ concat (intersperse " => "  (C.patSum <$> p)) ++ " => ..."

                -- loggg $ lfullshow w
                putStrLn ""

          pure $ Ok mod'' 


parseModule :: Path -> String -> Either ParseError Module
parseModule path s = prettyParse path s $ token modulep 

--TODO add more semantic info
data ReplRes a
  = ParseError ParseError
  | TypeError C.Err
  | SurfaceTypeError String 
  -- TODO bad path
  | Ok a
  deriving Show


data ReplCmd
  = Load String
  -- | LoadSurface String
  | TyInf Exp
  | Eval Exp
  | Whnf Exp
  | AllInfo Exp
  | Quit
  deriving Show



data ReplState
  = 
    -- Surface (Map TCName DataDef, Map Var (Term, Ty))
    Cast C.Module
  | NothingLoaded --TODO stdlib env?
  deriving Show


-- type for a single evaluation in the REPL
type REPLEval a =
  ReplState  -- state before eval
  -> a  -- expression to eval
  -> InputT IO (Maybe ReplState)  -- state after eval


  -- helper function to output an REPLState in the REPL functions
setREPLState :: ReplState -> InputT IO (Maybe ReplState)
setREPLState = return . return

-- action to execute when REPL load a file path with cast language
-- TODO catch errors thrown from loadFile
evalCastFilePath :: REPLEval FilePath
evalCastFilePath curState path =  do
  res <- lift $ loadFile path
  case res of
    Ok x -> do
      outputStrLn "loaded"
      -- loggg $ lfullshow x 
      setREPLState $ Cast x
    ParseError ls -> do
      outputStrLn "ParseError"
      outputStrLn $ show ls
      setREPLState curState

    TypeError e -> do
      outputStrLn "TypeError"
      outputStrLn $ C.prettyErr e
      setREPLState curState
    _ -> do
      outputStrLn "err"
      outputStrLn $ show res
      setREPLState curState



-- get type info for a cast language expression in REPL
getCastExpTypeInfo :: REPLEval (String, Exp, C.Module)
getCastExpTypeInfo curState (inpStr, exp, mod) = do
  let exp' = C.underModule exp mod -- add refferences from the loaded module
  mExp <- runExceptT $ runFreshMT $ C.runWithModuleMT (C.runWithSourceLocMT (C.elabInf' exp' (C.empElabInfo Dynamic.Norm.whnfd) ) (Just $ SourceRange (Just inpStr) (SourcePos "" 0 0) (endPos "" inpStr))) mod
  case mExp of
    Right (ctrm, cty) -> do
      -- putStrLn $ "elaborated to, " ++ show e
      outputStrLn $ show (runFreshM $ C.erase ctrm) ++ " : " ++ show (runFreshM $ C.erase cty)

    Left e -> do
      outputStrLn $ C.prettyErr e
  --   e -> do
  --     outputStrLn $ "catchall? " ++ show e
  setREPLState curState

-- evaluate a cast language expression in REPL
evalCastExp :: REPLEval (String, Exp, C.Module)
evalCastExp curState (inpStr, exp, mod) = do
  let exp' = C.underModule exp mod
  -- loggg $ lfullshow exp'
  mExp <- runExceptT $ runFreshMT $ C.runWithModuleMT (C.runWithSourceLocMT (C.elabInf' exp' (C.empElabInfo Dynamic.Norm.whnfd) ) (Just $ SourceRange (Just inpStr) (SourcePos "" 0 0) (endPos "" inpStr))) mod
  case mExp of
    Right (e,cty) -> do
      loggg $ lfullshow e
      outputStrLn $ show (runFreshM $ C.erase e)
      outputStrLn $ " : " ++ show (runFreshM $ C.erase cty)
      me' <- runExceptT $ runFreshMT $ C.runWithModuleMT (C.cbvOrErr e) mod
      case me' of
        Right e' -> do
          -- loggg $ lfullshow e'
          outputStrLn "~>"
          outputStrLn $ show (runFreshM $ C.erase e')
        Left (C.EqErr l (info@C.Info{C.sr=mrange}) _ r) -> do
          outputStrLn "unequal type assumption!!"
          case mrange of
            Just range -> outputStrLn $ unlines $ prettyRange range
            Nothing -> pure ()
          outputStrLn $ show info
          outputStrLn $ show info
          outputStrLn $ show (runFreshM $ C.erase l)
          outputStrLn $ " =/= "
          outputStrLn $ show (runFreshM $ C.erase r)
        Left (C.UnMatchedPatErr scruts pats mrange) -> do
          outputStrLn "unmatched pattern!!"
          case mrange of
            Just range -> outputStrLn $ unlines $ prettyRange range
            Nothing -> pure ()
          outputStrLn $ runFreshM $ do ghhh <- mapM C.erase scruts; pure $ concat (intersperse ", " (show <$> ghhh))
          -- TODO could do some fancy padding here
          outputStrLn $ "  | " ++ concat (intersperse " => "  (C.patSum <$> pats)) ++ " => ..."
    Left e -> do
      outputStrLn $ C.prettyErr e
  setREPLState curState

whnfCastExp :: REPLEval (String, Exp, C.Module)
whnfCastExp curState (inpStr, exp, mod) = do
  let exp' = C.underModule exp mod
  -- loggg $ lfullshow exp'
  mExp <- runExceptT $ runFreshMT $ C.runWithModuleMT (C.runWithSourceLocMT (C.elabInf' exp' (C.empElabInfo Dynamic.Norm.whnfd) ) (Just $ SourceRange (Just inpStr) (SourcePos "" 0 0) (endPos "" inpStr))) mod
  case mExp of
    Right (e,cty) -> do
      loggg $ lfullshow e
      outputStrLn $ show (runFreshM $ C.erase e)
      outputStrLn $ " : " ++ show (runFreshM $ C.erase cty)
      me' <- runExceptT $ runFreshMT $ C.runWithModuleMT (Dynamic.Norm.whnfd e) mod
      case me' of
        Right e' -> do
          loggg $ lfullshow e'
          outputStrLn "~>"
          outputStrLn $ show (runFreshM $ C.erase e')
        Left (C.EqErr l (info@C.Info{C.sr=mrange}) _ r) -> do
          outputStrLn "unequal type assumption!!"
          case mrange of
            Just range -> outputStrLn $ unlines $ prettyRange range
            Nothing -> pure ()
          outputStrLn $ show info
          outputStrLn $ show info
          outputStrLn $ show (runFreshM $ C.erase l)
          outputStrLn $ " =/= "
          outputStrLn $ show (runFreshM $ C.erase r)
        Left (C.UnMatchedPatErr scruts pats mrange) -> do
          outputStrLn "unmatched pattern!!"
          case mrange of
            Just range -> outputStrLn $ unlines $ prettyRange range
            Nothing -> pure ()
          outputStrLn $ runFreshM $ do ghhh <- mapM C.erase scruts; pure $ concat (intersperse ", " (show <$> ghhh))
          -- TODO could do some fancy padding here
          outputStrLn $ "  | " ++ concat (intersperse " => "  (C.patSum <$> pats)) ++ " => ..."
    Left e -> do
      outputStrLn $ C.prettyErr e
  setREPLState curState


-- TODO reload current file

-- eval the input string and print out the output once
-- If the output state is empty, that indicates termination of computation
evalREPLCom :: ReplState -> String -> InputT IO (Maybe ReplState)
evalREPLCom curState inpStr =
  case (parse (
    -- (do keyword ":ls"; path <- token $ some $ sat (/= '\n'); pure $ LoadSurface path) <|>
    (do keyword ":l"; path <- token $ some $ sat (/= '\n'); pure $ Load path) <|>
    (do keyword ":t"; e <- token exp;                       pure $ TyInf e  ) <|>
    (do keyword ":n"; e <- token exp;                       pure $ Eval e   ) <|>
    (do keyword ":w"; e <- token exp;                       pure $ Whnf e   ) <|>
    (do keyword ":q";                                       pure   Quit     ) <|>
    (do e <- token  exp;                                    pure $ AllInfo e)
    ) inpStr, curState) of

    -- quite
    (Right (Quit,_,_), _) -> do
      outputStrLn "bye"
      return Nothing

    -- load file
    (Right (Load path,_,""), _) -> evalCastFilePath curState path

    -- (Right (LoadSurface path,_,""), _) -> evalSurfaceFilePath curState path

    -- -- get type info
    -- (Right (TyInf exp,_,""), Surface (ddefs, trmdefs))->
    --   getSurfaceExpTypeInfo curState (inpStr, exp, ddefs, trmdefs)

    (Right (TyInf exp,_,""), Cast mod) ->
      getCastExpTypeInfo curState (inpStr, exp, mod)

    -- eval
    -- (Right (Eval exp,_,""), Surface (ddefs, trmdefs))->
    --   evalSurfaceExp curState (exp, ddefs, trmdefs)


    (Right (Whnf exp,_,""), Cast mod)->
      whnfCastExp curState (inpStr, exp, mod)

    (Right (Eval exp,_,""), Cast mod)->
      evalCastExp curState (inpStr, exp, mod)

    -- get all info
    -- (Right (AllInfo exp,_,""), Surface (ddefs, trmdefs)) ->
    --   allInfoSurfaceExp curState (exp, ddefs, trmdefs)

    (Right (AllInfo exp,_,""), Cast mod) ->
      evalCastExp curState (inpStr, exp, mod)
      -- allInfoCastExp curState (inpStr, exp, mod)

    -- parse error
    (ee, _) -> do
      outputStrLn "unknown cmd"
      outputStrLn $ show ee
      setREPLState curState

-- BUG: file autocomplete is always on
-- BUG: file autocomplete adds unreadable space to teh end of input
repl :: IO ()
repl = runInputT defaultSettings (loop NothingLoaded)
  where
    loop curState = do
      input <- getInputLine "dt> "
      case input of
        Nothing -> return ()
        Just inputStr -> do
          res <- evalREPLCom curState inputStr
          Data.Foldable.forM_ res loop





-- from https://en.wikibooks.org/wiki/Write_Yourself_a_Scheme_in_48_Hours/Building_a_REPL
flushStr :: String -> IO ()
flushStr str = putStr str >> hFlush stdout

readPrompt :: String -> IO String
readPrompt prompt = flushStr prompt >> getLine


-- TODO
-- cross instance up arrow competion
-- https://github.com/judah/haskeline ?

-- Some other repls for refference
-- https://github.com/diku-dk/futhark/blob/ee780c984227ed59548a16fa6ab6d8b52348a7a4/src/Futhark/CLI/REPL.hs


e0 = loadFile "ex/e.dt"

-- e = loadFile "examples/ex1.dt"
-- e1 = loadFile "ex1_bad.dt"


-- e2 = loadSurfaceFile "examples/motive.dt"
