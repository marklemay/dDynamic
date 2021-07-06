{-# LANGUAGE ViewPatterns #-}

module Parser where
import Control.Monad(ap)

import Prelude hiding((^^), exp, pi)
import Data.Either

import Data.Map (Map)
import qualified Data.Map as Map

import ParserMonad  hiding(spaces)
import Ast
import UnboundHelper
import Unbound.Generics.LocallyNameless

import qualified StdLib
import qualified Helper
import qualified Env


import Data.Char

comment :: Parser ()
comment = do
  literal "--"
  rep $ sat (/= '\n')
  sat (== '\n') <|> pure '\n' -- for comment in last line of the file
  pure ()


--parse spaces, throw them away
spacesOrComments :: Parser ()
spacesOrComments = do 
  rep (sat isSpace)
  (do comment; spacesOrComments) <|> pure ()
  

token :: Parser a -> Parser a
token pa = do 
  spacesOrComments
  a <- pa
  spacesOrComments
  pure a


keyword :: String -> Parser String
keyword s = token $ literal s

-- it is left associative
withInfix :: Parser a -> [(String, a -> a -> a)] -> Parser a
withInfix pa ls = let 
  operators = fmap fst ls
  opParsers = fmap (\ s -> token $ literal s) operators

  --innerParser :: a -> Parser a, where a is the same as above
  innerParser left = do 
    s <- oneOf opParsers
    next <- pa
    case lookup s ls of
      Nothing -> error "this should be impossible"
      Just f ->  let out = f left next
                  in (innerParser out) <|> pure out
  in do 
    l <- pa
    (innerParser l) <|> (pure l)



--TODO: exclude keyword(s) from identifiers

loc :: Parser Exp -> Parser Exp
loc p = do
  s <- gets
  x <- p
  s' <- gets
  pure $ Pos s x s'

tokenl :: Parser Exp -> Parser Exp
tokenl pa = do 
  spacesOrComments
  a <- loc pa
  spacesOrComments
  pure a

keywords = ["case"]

nameParser :: Parser (Name a)
nameParser = s2n <$> nameParser'

nameParser' :: Parser String
nameParser' = do
  ident <- identifierParser
  if ident `elem` keywords
    then failParse $ "'" ++ ident ++ "' is a keword used as an identifier"
    else pure ident


withInfixl :: Parser Exp -> [(String, Exp -> Exp -> Exp)] -> Parser Exp
withInfixl pa ls = let 
  operators = fmap fst ls
  opParsers = fmap (\ s -> token $ literal s) operators

  --innerParser :: a -> Parser a, where a is the same as above
  innerParser left = do 
    s <- oneOf opParsers
    next <- pa
    case lookup s ls of
      Nothing -> error "this should be impossible"
      Just f ->  let out = f left next
                  in (tokenl $ innerParser out) <|> pure out
  in do 
    l <- tokenl pa
    innerParser l <|> pure l


exp :: Parser Exp
exp = pi <|> (do
  e <- exp2
  (tokenl $ do 
    literal "->" 
    e2 <- exp
    pure $ Pi e $ bind unnamed e2
    ) <|> pure e)
    -- TODO: could be much more efficient


exp2 :: Parser Exp
exp2 = do
  e <- exp1
  (tokenl $ do 
    literal ":" 
    e2 <- exp2
    pure $ e ::: e2
    ) <|> pure e

exp1 :: Parser Exp
exp1 = exp0 `withInfixl` [("", App)] 

exp0 :: Parser Exp
exp0 = (tokenl $
  (do literal "*"; pure TyU) <|>
  (do literal "?"; pure $ Solve noAn) <|>
  fun  <|> lam <|> elim <|> --pi <|> 
  (do i <- natParser; pure $ StdLib.n i) <|> -- stdlib hack
  vec <|>
  (do v <- nameParser; pure $ V v) 
  ) <|> (do keyword "("; e<-exp;keyword ")"; pure e) 

 -- stdlib hack
vec :: Parser Exp
vec = do
  keyword "["
  es <- (do 
    e <- exp
    es <- rep (do keyword ","; exp)
    pure $ e:es) <|> pure []
  keyword "]"
  keyword "<"
  ty <- exp
  keyword ">"
  pure $ StdLib.ls es ty



fun :: Parser Exp
fun = do 
  keyword "fun"
  f <- token $ nameParser
  x <- token $ nameParser
  keyword "=>"
  e <- exp
  pure $ Fun $ bind (f, x) $ e


lam :: Parser Exp
lam = do 
  keyword "\\"
  x <- token $ nameParser
  keyword "=>"
  e <- exp
  pure $ Fun $ bind (unnamed, x) $ e

pi :: Parser Exp
pi = do 
  keyword "("
  x <- token $ nameParser
  keyword ":"
  aty <- exp
  keyword ")"
  keyword "->"
  e <- exp
  pure $ Pi aty $ bind x $ e


elim :: Parser Exp
elim = do 
  keyword "case"
  scrut <- exp
  motive <- (do 
    keyword "<"
    x <- token nameParser
    keyword ":"
    _ <- token nameParser -- a little hacky
    params <- rep $ token nameParser
    keyword "=>"
    bodTy <- exp
    keyword ">"
    pure $ Just (bind (x, params) bodTy)
    ) <|> pure Nothing
  keyword "{"
  branches <- rep $ do
    keyword "|"
    dCName <- token $ nameParser'
    args <- rep (token $ nameParser)
    keyword "=>"
    bod <- exp
    pure $ Match dCName $ bind (args) bod
  keyword "}"
  pure $ Case scrut (An motive) branches

modulep :: Parser (Map TCName DataDef, Map Var (Term, Ty))
modulep = do
  e <- rep $ do d <- datadef <||> termdef; keyword ";"; pure d
  let (Map.fromList -> datas, Map.fromList -> terms) = partitionEithers e
  pure $ Env.undermodule (datas, terms) datas

datadef :: Parser (TCName, DataDef)
datadef = do
  keyword "data"
  tCName <- token nameParser'
  keyword ":"
  tel <- telParser (do keyword "*"; pure ())
  keyword "{"
  cls <- rep $ do
    keyword "|"
    dCName <- token nameParser'
    keyword ":"
    tel <- telParser $ do 
      keyword tCName
      rep $ token exp0
    pure (dCName, tel)
  keyword "}"
  pure (tCName, DataDef tel $ Map.fromList cls)


termdef :: Parser (Var, (Term, Ty))
termdef = do
  x <- token nameParser'
  keyword ":"
  ty <- exp
  keyword ";"
  keyword x
  largs <- rep $ token nameParser
  keyword "="
  bod <- exp
  pure (s2n x, (lamall largs bod, ty))



lamall :: [Var] -> Exp -> Exp
lamall [] e = e 
lamall (h:t) e = Helper.lam h $ lamall t e 


--TODO generalize?
-- TODO also doesn't suport nested parens
telParser :: (Alpha a) => Parser a -> Parser (Tel Exp Exp a)
telParser pa = 
  (do 
    keyword "("
    x <- token nameParser
    keyword ":"
    ty <- exp
    keyword ")"
    keyword "->" 
    tel <- telParser pa
    pure $ TelBnd ty (bind x tel))  <|> 
  (do
    ty <- exp2
    keyword "->" 
    tel <- telParser pa
    pure $ TelBnd ty (u tel)) <|> 
  (NoBnd <$> pa)
  
  
-- TODO fix bug:  (fun f x => 1) : (Nat -> Nat) to   (fun f x => 1) : Nat -> Nat
-- TODO bake s2n into the var parser?
-- TODO make sure there is no keyword overlap