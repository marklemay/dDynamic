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
evalFilePath :: REPLEval string
evalFilePath curState path =  do
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
evalSurfaceFilePath :: REPLEval string
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


-- get type info for a cast language expression in REPL
getCastExpTypeInfo :: REPLEval (String, Exp, Map TCName DataDef, Map Var (Term, Ty) )
getCastExpTypeInfo curState (expStr, exp, ddefs, trmdefs) = do
  let exp' = undermodule exp ddefs
  case runTcMonadS "" expStr (TyEnv Map.empty ddefs trmdefs) $ tyInfer exp' of
    Right a -> outputStrLn $ show a
    Left s -> outputStrLn s
  setREPLState curState


-- get type info for a surface language expression in REPL
getSurfaceExpTypeInfo :: REPLEval (String, Exp, Map TCName C.DataDef, Map C.Var C.Term )
getSurfaceExpTypeInfo curState (expStr, exp, ddefs, trmdefs) = do
  let mod = C.makeMod ddefs trmdefs
  let exp' = C.undermodule exp mod
  case C.runC (do
      e'' <- C.elabInf exp' Map.empty Map.empty
      C.whnfann e''
      )
    mod
    (Just $ SourceRange (Just expStr) (SourcePos "" 0 0) (endPos "" expStr)) of
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



-- eval the input string and print out the output once
-- If the output state is empty, that indicates termination of computation
evalREPLCom :: ReplState -> String -> InputT IO (Maybe ReplState)
evalREPLCom m s =
  case (parse (
    (do keyword ":ls"; path <- token $ some $ sat (/= '\n'); pure $ LoadSurface path) <|>
    (do keyword ":l"; path <- token $ some $ sat (/= '\n'); pure $ Load path) <|>
    (do keyword ":t"; e <- token exp;                       pure $ TyInf e  ) <|>
    (do keyword ":n"; e <- token exp;                       pure $ Eval e   ) <|>
    (do keyword ":q";                                       pure   Quit     ) <|>
    (do e <- token  exp;                                    pure $ AllInfo e)
    ) s, m) of
    (Right (Quit,_,_), _) -> do
      outputStrLn "bye"
      return Nothing

    (Right (Load path,_,""), _) -> do
      res <- loadFile path
      case res of
        Ok x -> do
          outputStrLn "loaded"
          -- putStrLn $ show x
          repl' $ Cast x
        ParseError ls -> do
          outputStrLn "ParseError"
          putStrLn $ unlines ls
          repl' m

        TypeError e -> do
          outputStrLn "TypeError"
          outputStrLn $ C.prettyErr e
          repl' m
        _ -> do
          outputStrLn "err"
          outputStrLn $ show res
          repl' m


    (Right (LoadSurface path,_,""), _) -> do
      putStrLn path
      res <- loadSurfaceFile path
      case res of
        Ok x -> do
          putStrLn "loaded"
          -- putStrLn $ show x
          repl' $ Surface x
        ParseError ls -> do
          putStrLn "ParseError"
          putStrLn $ unlines ls
          repl' m

        SurfaceTypeError s -> do
          putStrLn "SurfaceTypeError"
          putStrLn s
          repl' m
        _ -> do
          putStrLn "err"
          putStrLn $ show res
          repl' m
    (Right (TyInf e,_,""), Surface (ddefs, trmdefs))-> do
      let e' = undermodule e ddefs
      -- case runTcMonadS "" s (TyEnv Map.empty  (dataCtx stdlib `Map.union` ddefs) (defCtx stdlib `Map.union` trmdefs)) $ tyInfer e' of
      case runTcMonadS "" s (TyEnv Map.empty ddefs trmdefs) $ tyInfer e' of

        Right a -> outputStrLn $ show a
        Left s -> outputStrLn s
      repl' m

    (Right (TyInf e,_,""), Cast (ddefs, trmdefs)) -> do
      let mod = C.makeMod ddefs trmdefs
      let e' = C.undermodule e mod
      case C.runC (do
          e'' <- C.elabInf e' Map.empty Map.empty
          C.whnfann e''
          )
        mod
        (Just $ SourceRange (Just s) (SourcePos "" 0 0) (endPos "" s)) of
        Right e@(C.tyInf -> Just ty) -> do
          -- putStrLn $ "elaborated to, " ++ show e
          putStrLn $ " : " ++ show (C.e ty)

        Right e@(C.tyInf -> Nothing) -> do
          putStrLn $ "elaborated to , " ++ show e
          putStrLn "could not infer the type"

        Left e -> do
          putStrLn $ C.prettyErr e
        e -> do
          putStrLn $ "catchall? " ++ show e
      repl' m

    (Right (Eval e,_,""), Surface (ddefs, trmdefs))-> do
      let e' = undermodule e ddefs
      -- let res = runTcMonad (TyEnv Map.empty  (dataCtx stdlib `Map.union` ddefs) (defCtx stdlib `Map.union` trmdefs)) $ cbv e'
      let res = runTcMonad (TyEnv Map.empty  ddefs trmdefs) $ cbv e'
      putStrLn $ show res
      repl' m


    (Right (Eval e,_,""), Cast (ddefs, trmdefs))-> do
      let mod = C.makeMod ddefs trmdefs
      let e' = C.undermodule e mod
      case C.runC (do
          e'' <- C.elabInf e' Map.empty Map.empty
          C.cbvCheck e''
          )
        mod
        (Just $ SourceRange (Just s) (SourcePos "" 0 0) (endPos "" s)) of
          Right e -> do
            putStrLn $ show $ C.e e
          Left e -> do
            putStrLn $ C.prettyErr e
      repl' m

    (Right (AllInfo e,_,""), Surface (ddefs, trmdefs)) -> do
      -- let e' = undermodule e (dataCtx stdlib `Map.union` ddefs)
      -- putStrLn $ show $ runTcMonad (TyEnv Map.empty  (dataCtx stdlib `Map.union` ddefs) (defCtx stdlib `Map.union` trmdefs)) $ tyInfer e'
      -- putStrLn $ show $ runTcMonad (TyEnv Map.empty  (dataCtx stdlib `Map.union` ddefs) (defCtx stdlib `Map.union` trmdefs)) $ safeEval e'
      let e' = undermodule e ddefs
      putStrLn $ show $ runTcMonad (TyEnv Map.empty ddefs trmdefs) $ tyInfer e'
      putStrLn $ show $ runTcMonad (TyEnv Map.empty ddefs trmdefs) $ cbv e'
      repl' m

    (Right (AllInfo e,_,""), Cast (ddefs, trmdefs)) -> do

      let mod = C.makeMod ddefs trmdefs
      let e' = C.undermodule e mod

      case C.runC (do
          e'' <- C.elabInf e' Map.empty Map.empty
          C.cbvCheck e''
          )
        mod
        (Just $ SourceRange (Just s) (SourcePos "" 0 0) (endPos "" s)) of
          Right e -> do
            putStrLn $ show $ C.e e
          Left e -> do
            putStrLn $ C.prettyErr e

      case C.runC (do
          e'' <- C.elabInf e' Map.empty Map.empty
          C.whnfann e''
          )
        mod
        (Just $ SourceRange (Just s) (SourcePos "" 0 0) (endPos "" s)) of
        Right (e@(C.tyInf -> Just ty)) -> do --TODO eval the ty for presentation!
          -- putStrLn $ "elaborated to, " ++ show e
          putStrLn $ " : " ++ show (C.e ty)
        Right (e@(C.tyInf -> Nothing)) -> do
          putStrLn $ "elaborated to , " ++ show e
          putStrLn "could not infer the type"

        Left e -> do
          putStrLn $ C.prettyErr e
        e -> do
          putStrLn $ "catchall? " ++ show e
      repl' m

    (ee, _) -> do
      putStrLn "unknown cmd"
      print ee
      repl' m




-- TODO eat blank cmds
repl' :: ReplState -> InputT IO ()
repl' m = do
  s <- getInputLine "dt> "
  -- putStrLn s
  case (parse (
    (do keyword ":ls"; path <- token $ some $ sat (/= '\n'); pure $ LoadSurface path) <|>
    (do keyword ":l"; path <- token $ some $ sat (/= '\n'); pure $ Load path) <|>
    (do keyword ":t"; e <- token exp;                       pure $ TyInf e  ) <|>
    (do keyword ":n"; e <- token exp;                       pure $ Eval e   ) <|>
    (do keyword ":q";                                       pure   Quit     ) <|>
    (do e <- token  exp;                                    pure $ AllInfo e)
    ) s, m) of
    (Right (Quit,_,_), _) -> outputStrLn "bye"

    (Right (Load path,_,""), _) -> do
      res <- return . loadFile $ path

      case res of
        Ok x -> do
          putStrLn "loaded"
          -- putStrLn $ show x
          repl' $ Cast x
        ParseError ls -> do
          putStrLn "ParseError"
          putStrLn $ unlines ls
          repl' m

        TypeError e -> do
          putStrLn "TypeError"
          putStrLn $ C.prettyErr e
          repl' m
        _ -> do
          putStrLn "err"
          putStrLn $ show res
          repl' m


    (Right (LoadSurface path,_,""), _) -> do
      putStrLn path
      res <- loadSurfaceFile path
      case res of
        Ok x -> do
          putStrLn "loaded"
          -- putStrLn $ show x
          repl' $ Surface x
        ParseError ls -> do
          putStrLn "ParseError"
          putStrLn $ unlines ls
          repl' m

        SurfaceTypeError s -> do
          putStrLn "SurfaceTypeError"
          putStrLn s
          repl' m
        _ -> do
          putStrLn "err"
          putStrLn $ show res
          repl' m
    (Right (TyInf e,_,""), Surface (ddefs, trmdefs))-> do
      let e' = undermodule e ddefs
      -- case runTcMonadS "" s (TyEnv Map.empty  (dataCtx stdlib `Map.union` ddefs) (defCtx stdlib `Map.union` trmdefs)) $ tyInfer e' of
      case runTcMonadS "" s (TyEnv Map.empty ddefs trmdefs) $ tyInfer e' of

        Right a -> putStrLn $ show a
        Left s -> putStrLn s
      repl' m

    (Right (TyInf e,_,""), Cast (ddefs, trmdefs)) -> do
      let mod = C.makeMod ddefs trmdefs
      let e' = C.undermodule e mod
      case C.runC (do
          e'' <- C.elabInf e' Map.empty Map.empty
          C.whnfann e''
          )
        mod
        (Just $ SourceRange (Just s) (SourcePos "" 0 0) (endPos "" s)) of
        Right e@(C.tyInf -> Just ty) -> do
          -- putStrLn $ "elaborated to, " ++ show e
          putStrLn $ " : " ++ show (C.e ty)

        Right e@(C.tyInf -> Nothing) -> do
          putStrLn $ "elaborated to , " ++ show e
          putStrLn "could not infer the type"

        Left e -> do
          putStrLn $ C.prettyErr e
        e -> do
          putStrLn $ "catchall? " ++ show e
      repl' m

    (Right (Eval e,_,""), Surface (ddefs, trmdefs))-> do
      let e' = undermodule e ddefs
      -- let res = runTcMonad (TyEnv Map.empty  (dataCtx stdlib `Map.union` ddefs) (defCtx stdlib `Map.union` trmdefs)) $ cbv e'
      let res = runTcMonad (TyEnv Map.empty  ddefs trmdefs) $ cbv e'
      putStrLn $ show res
      repl' m


    (Right (Eval e,_,""), Cast (ddefs, trmdefs))-> do
      let mod = C.makeMod ddefs trmdefs
      let e' = C.undermodule e mod
      case C.runC (do
          e'' <- C.elabInf e' Map.empty Map.empty
          C.cbvCheck e''
          )
        mod
        (Just $ SourceRange (Just s) (SourcePos "" 0 0) (endPos "" s)) of
          Right e -> do
            putStrLn $ show $ C.e e
          Left e -> do
            putStrLn $ C.prettyErr e
      repl' m

    (Right (AllInfo e,_,""), Surface (ddefs, trmdefs)) -> do
      -- let e' = undermodule e (dataCtx stdlib `Map.union` ddefs)
      -- putStrLn $ show $ runTcMonad (TyEnv Map.empty  (dataCtx stdlib `Map.union` ddefs) (defCtx stdlib `Map.union` trmdefs)) $ tyInfer e'
      -- putStrLn $ show $ runTcMonad (TyEnv Map.empty  (dataCtx stdlib `Map.union` ddefs) (defCtx stdlib `Map.union` trmdefs)) $ safeEval e'
      let e' = undermodule e ddefs
      putStrLn $ show $ runTcMonad (TyEnv Map.empty ddefs trmdefs) $ tyInfer e'
      putStrLn $ show $ runTcMonad (TyEnv Map.empty ddefs trmdefs) $ cbv e'
      repl' m

    (Right (AllInfo e,_,""), Cast (ddefs, trmdefs)) -> do

      let mod = C.makeMod ddefs trmdefs
      let e' = C.undermodule e mod

      case C.runC (do
          e'' <- C.elabInf e' Map.empty Map.empty
          C.cbvCheck e''
          )
        mod
        (Just $ SourceRange (Just s) (SourcePos "" 0 0) (endPos "" s)) of
          Right e -> do
            putStrLn $ show $ C.e e
          Left e -> do
            putStrLn $ C.prettyErr e

      case C.runC (do
          e'' <- C.elabInf e' Map.empty Map.empty
          C.whnfann e''
          )
        mod
        (Just $ SourceRange (Just s) (SourcePos "" 0 0) (endPos "" s)) of
        Right (e@(C.tyInf -> Just ty)) -> do --TODO eval the ty for presentation!
          -- putStrLn $ "elaborated to, " ++ show e
          putStrLn $ " : " ++ show (C.e ty)
        Right (e@(C.tyInf -> Nothing)) -> do
          putStrLn $ "elaborated to , " ++ show e
          putStrLn "could not infer the type"

        Left e -> do
          putStrLn $ C.prettyErr e
        e -> do
          putStrLn $ "catchall? " ++ show e
      repl' m

    (ee, _) -> do
      putStrLn "unknown cmd"
      print ee
      repl' m


repl = repl' NothingLoaded -- $ Surface (Map.empty, Map.empty)



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
