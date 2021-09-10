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


module Repl where

import Unbound.Generics.LocallyNameless
import GHC.Generics (Generic, SourceStrictness (SourceStrict))
import Data.Typeable (Typeable)


import Data.Map (Map)
import qualified Data.Map as Map

import Data.Monoid (Any(..))
import Control.Applicative (Applicative(..), (<$>))
import Unbound.Generics.LocallyNameless.Internal.Fold (foldMapOf, toListOf)

import Control.Monad.Except (catchError, MonadError(throwError))
import Control.Monad (guard) -- TODO: need a version with string error
import Control.Monad.Reader

-- for command line features
import System.Console.Haskeline

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
import qualified Dynamic.Err as C
import qualified Dynamic.Elab as C
import qualified Dynamic.ElabModule as C
import qualified Dynamic.Env as C
import qualified Dynamic.Helper as C
import qualified Dynamic.Erase as C


--TODO clean this up
type Module = (Map TCName DataDef, Map Var (Term, Ty))

-- runFile :: FilePath -> IO LangOut
-- runFile path = 
--   do program <- readFile path
--      return $ exec program


loadFile path = do
  s <- readFile path
  -- print s
  case pmstd path s of
    Right m@(ddefs,trmdefs) -> do
      putStrLn "parsed"
      -- TODO easier to debug if the entire std lib is loaded first, will give incorrect source ranges!
      case C.elabmodule (TyEnv
        Map.empty
        ddefs
        trmdefs) $ Just $ SourceRange (Just s) (SourcePos path 0 0) (endPos path s) of
        Right ((ddefs,trmdefs),_) ->  do
          putStrLn "elaborated"
          -- putStrLn $ show m
          pure $ Ok (ddefs,trmdefs)
        Left e ->  do

          putStrLn ""
          putStrLn ""
          putStrLn $ C.prettyErr e
          putStrLn ""
          putStrLn ""
          putStrLn ""

          pure $ TypeError e
    Left ls -> pure $ ParseError ls


loadSurfaceFile :: FilePath -> IO (ReplRes (Map TCName DataDef, Map Var (Term, Ty)))
loadSurfaceFile path = do
  s <- readFile path
  -- print s
  case pmstd path s of
    Right m@(ddefs,trmdefs) -> do
      putStrLn "parsed"
      -- TODO easier to debug if the entire std lib is loaded first, will give incorrect source ranges!
      case runTcMonadS path s (TyEnv
        Map.empty
        ddefs -- (dataCtx stdlib `Map.union` ddefs) 
        trmdefs -- (defCtx stdlib `Map.union` trmdefs) ) 
        ) envWf of
        Right () ->  do
          putStrLn "typechecked"
          -- putStrLn $ show m
          pure $ Ok (ddefs,trmdefs)
        Left e ->  do
          pure $ SurfaceTypeError e
    Left ls -> pure $ ParseError ls

-- pmstd :: String ->  String -> Maybe ((Map TCName DataDef, Map Var (Term, Ty)), String)
pmstd path s = prettyParse path s $ do
  token modulep
  -- pure $ undermodule e (dataCtx stdlib)

--TODO add more semantic info
data ReplRes a
  = ParseError [String]
  | TypeError C.Err
  | SurfaceTypeError String
  -- TODO bad path
  | Ok a
  deriving Show


data ReplCmd
  = Load String
  | LoadSurface String
  | TyInf Exp
  | Eval Exp
  | AllInfo Exp
  | Quit
  deriving Show



data ReplState
  = Surface (Map TCName DataDef, Map Var (Term, Ty))
  | Cast (Map TCName C.DataDef, Map C.Var C.Term)
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
evalCastFilePath :: REPLEval FilePath 
evalCastFilePath curState path =  do
  res <- lift $ loadFile path
  case res of
    Ok x -> do
      outputStrLn "loaded"
      setREPLState $ Cast x
    ParseError ls -> do
      outputStrLn "ParseError"
      outputStrLn $ unlines ls
      setREPLState curState

    TypeError e -> do
      outputStrLn "TypeError"
      outputStrLn $ C.prettyErr e
      setREPLState curState
    _ -> do
      outputStrLn "err"
      outputStrLn $ show res
      setREPLState curState


-- action to execute when REPL load a file with surface language
evalSurfaceFilePath :: REPLEval FilePath 
evalSurfaceFilePath curState path =  do
  res <- lift $ loadSurfaceFile path
  case res of
    Ok x -> do
      outputStrLn "loaded"
      setREPLState $ Surface x
    ParseError ls -> do
      outputStrLn "ParseError"
      outputStrLn $ unlines ls
      setREPLState curState

    SurfaceTypeError s -> do
      outputStrLn "SurfaceTypeError"
      outputStrLn s
      setREPLState curState

    _ -> do
      outputStrLn "err"
      outputStrLn $ show res
      setREPLState curState


-- get type info for a surface language expression in REPL
getSurfaceExpTypeInfo :: REPLEval (String, Exp, Map TCName DataDef, Map Var (Term, Ty) )
getSurfaceExpTypeInfo curState (inpStr, exp, ddefs, trmdefs) = do
  let exp' = undermodule exp ddefs
  case runTcMonadS "" inpStr (TyEnv Map.empty ddefs trmdefs) $ tyInfer exp' of
    Right a -> outputStrLn $ show a
    Left s -> outputStrLn s
  setREPLState curState


-- get type info for a cast language expression in REPL
getCastExpTypeInfo :: REPLEval (String, Exp, Map TCName C.DataDef, Map C.Var C.Term )
getCastExpTypeInfo curState (inpStr, exp, ddefs, trmdefs) = do
  let mod = C.makeMod ddefs trmdefs
  let exp' = C.undermodule exp mod
  case C.runC (do
      e'' <- C.elabInf exp' Map.empty Map.empty
      C.whnfann e''
      )
    mod
    (Just $ SourceRange (Just inpStr) (SourcePos "" 0 0) (endPos "" inpStr)) of
    Right e@(C.tyInf -> Just ty) -> do
      -- putStrLn $ "elaborated to, " ++ show e
      outputStrLn $ " : " ++ show (C.e ty)

    Right e@(C.tyInf -> Nothing) -> do
      outputStrLn $ "elaborated to , " ++ show e
      outputStrLn "could not infer the type"

    Left e -> do
      outputStrLn $ C.prettyErr e
    e -> do
      outputStrLn $ "catchall? " ++ show e
  setREPLState curState


-- evaluate a cast language expression in REPL
evalSurfaceExp :: REPLEval (Exp, Map TCName DataDef, Map Var (Term, Ty) )
evalSurfaceExp curState (exp, ddefs, trmdefs) = do
  let exp' = undermodule exp ddefs
  let res = runTcMonad (TyEnv Map.empty  ddefs trmdefs) $ cbv exp
  outputStrLn $ show res
  setREPLState curState

-- evaluate a surface language expression in REPL
evalCastExp :: REPLEval (String, Exp, Map TCName C.DataDef, Map C.Var C.Term )
evalCastExp curState (inpStr, exp, ddefs, trmdefs) = do
  let mod = C.makeMod ddefs trmdefs
  let exp' = C.undermodule exp mod
  case C.runC (do
      e'' <- C.elabInf exp' Map.empty Map.empty
      C.cbvCheck e''
      )
    mod
    (Just $ SourceRange (Just inpStr) (SourcePos "" 0 0) (endPos "" s)) of
      Right e -> do
        outputStrLn $ show $ C.e e
      Left e -> do
        outputStrLn $ C.prettyErr e
  setREPLState curState


-- get all info for a cast language expression in REPL
allInfoSurfaceExp :: REPLEval (Exp, Map TCName DataDef, Map Var (Term, Ty) )
allInfoSurfaceExp curState (exp, ddefs, trmdefs) = do
  let exp' = undermodule exp ddefs
  outputStrLn $ show $ runTcMonad (TyEnv Map.empty ddefs trmdefs) $ tyInfer exp'
  outputStrLn $ show $ runTcMonad (TyEnv Map.empty ddefs trmdefs) $ cbv exp'
  setREPLState curState

-- get all info for a surface language expression in REPL
allInfoCastExp :: REPLEval (String, Exp, Map TCName C.DataDef, Map C.Var C.Term )
allInfoCastExp curState (inpStr, exp, ddefs, trmdefs) = do
  let mod = C.makeMod ddefs trmdefs
  let exp' = C.undermodule exp mod

  case C.runC (do
      exp'' <- C.elabInf exp' Map.empty Map.empty
      C.cbvCheck exp''
      )
    mod
    (Just $ SourceRange (Just inpStr) (SourcePos "" 0 0) (endPos "" inpStr)) of
      Right exp -> do
        outputStrLn $ show $ C.e exp
      Left exp -> do
        outputStrLn $ C.prettyErr exp

  case C.runC (do
      exp'' <- C.elabInf exp' Map.empty Map.empty
      C.whnfann exp''
      )
    mod
    (Just $ SourceRange (Just inpStr) (SourcePos "" 0 0) (endPos "" inpStr)) of
    Right e@(C.tyInf -> Just ty) -> do --TODO eval the ty for presentation!

      -- putStrLn $ "elaborated to, " ++ show e
      outputStrLn $ " : " ++ show (C.e ty)
    Right e@(C.tyInf -> Nothing) -> do
      outputStrLn $ "elaborated to , " ++ show e
      outputStrLn "could not infer the type"

    Left e -> do
      outputStrLn $ C.prettyErr e
    e -> do
      outputStrLn $ "catchall? " ++ show e
  setREPLState curState





-- eval the input string and print out the output once
-- If the output state is empty, that indicates termination of computation
evalREPLCom :: ReplState -> String -> InputT IO (Maybe ReplState)
evalREPLCom curState inpStr =
  case (parse (
    (do keyword ":ls"; path <- token $ some $ sat (/= '\n'); pure $ LoadSurface path) <|>
    (do keyword ":l"; path <- token $ some $ sat (/= '\n'); pure $ Load path) <|>
    (do keyword ":t"; e <- token exp;                       pure $ TyInf e  ) <|>
    (do keyword ":n"; e <- token exp;                       pure $ Eval e   ) <|>
    (do keyword ":q";                                       pure   Quit     ) <|>
    (do e <- token  exp;                                    pure $ AllInfo e)
    ) inpStr, curState) of

    -- quite
    (Right (Quit,_,_), _) -> do
      outputStrLn "bye"
      return Nothing

    -- load file
    (Right (Load path,_,""), _) -> evalCastFilePath curState path

    (Right (LoadSurface path,_,""), _) -> evalSurfaceFilePath curState path

    -- get type info
    (Right (TyInf exp,_,""), Surface (ddefs, trmdefs))-> 
      getSurfaceExpTypeInfo curState (inpStr, exp, ddefs, trmdefs)

    (Right (TyInf exp,_,""), Cast (ddefs, trmdefs)) ->
      getCastExpTypeInfo curState (inpStr, exp, ddefs, trmdefs)

    -- eval
    (Right (Eval exp,_,""), Surface (ddefs, trmdefs))->
      evalSurfaceExp curState (exp, ddefs, trmdefs)

    (Right (Eval exp,_,""), Cast (ddefs, trmdefs))->
      evalCastExp curState (inpStr, exp, ddefs, trmdefs) 

    -- get all info
    (Right (AllInfo exp,_,""), Surface (ddefs, trmdefs)) ->
      allInfoSurfaceExp curState (exp, ddefs, trmdefs)

    (Right (AllInfo exp,_,""), Cast (ddefs, trmdefs)) ->
      allInfoCastExp curState (inpStr, exp, ddefs, trmdefs)

    -- parse error
    (ee, _) -> do
      outputStrLn "unknown cmd"
      outputStrLn $ show ee
      setREPLState curState


repl :: IO ()
repl = runInputT defaultSettings (loop NothingLoaded)
  where 
    loop curState = do 
      input <- getInputLine "dt> "
      case input of 
        Nothing -> return ()
        Just inputStr -> do
          res <- evalREPLCom curState inputStr
          case res of 
            Nothing -> return ()
            Just newState -> loop newState




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

e0 = loadFile "examples/ex0.dt"

e = loadFile "examples/ex1.dt"
e1 = loadFile "ex1_bad.dt"


e2 = loadSurfaceFile "examples/motive.dt"
