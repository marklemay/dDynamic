-- origionally from https://github.com/BU-CS320/Summer-2019/blob/master/assignments/HW4/src/ParserMonad.hs

module ParserMonad where

import GHC.Stack

import Control.Monad(ap)
import SourcePos hiding (endPos)

import Data.Char

import PreludeHelper

-- the type of a parser
newtype Parser a = Parser (SourcePos -> String -> Either (String, SourcePos, SourcePos) (a, SourcePos, String))

-- a helper function to pull out the function bit (same as book)

parse :: Parser a
  -> String
  -> Either (String, SourcePos, SourcePos) (a, SourcePos, String)
parse (Parser f) = f $ SourcePos "" 0 0

runParse (Parser f) = f

parseIo :: HasCallStack => Parser a -> String -> IO a
parseIo pa s = do
  let res = parse pa s 
  case res of
    Left (_,start, end) -> errIo $ unlines $ prettyRange $ SourceRange (Just s) start end-- TODO need to double check this is catchable
    Right (a,_,"") -> pure a
    Right (a,_,rest) -> do
      logg $ "warning excess string: " ++ rest -- TODO print haskell stacktrace
      pure a


prettyParse :: String -> String -> Parser b -> Either [String] b
prettyParse path str p =
  case runParse (untillEnd p) (SourcePos path 0 0) str of
    Right (a,_,"") -> Right a
    Left (msg, s, s')  -> Left $ [
       msg
      , show s] ++ prettyRange' str s s'
    Right (a,_,rest) -> do
      logg $ "warning excess string: " ++ rest -- TODO print haskell stacktrace
      pure a
      
instance Functor Parser where
  fmap f (Parser pa) =
    Parser $ \ s x ->
      case pa s x of
        Left e -> Left e
        Right (a, pos, rest) -> Right (f a, pos, rest)

instance Applicative Parser where
  pure = return
  (<*>) = ap

instance Monad Parser where
  return a = 
    Parser $ \ s x -> Right (a,s,x)

  (Parser pa) >>= f = 
    Parser $ \ s x ->
      case pa s x of
        Left e -> Left e
        Right (a,s',rest) -> runParse (f a) s' rest


failParse str = Parser $ \ s _ -> Left (str, s, s)
failParse' s str = Parser $ \ s' _ -> Left (str, s, s')

gets = Parser $ \ s rest -> Right (s,s,rest)

-- with exception
-- TODO rename
withexp p ex = Parser $ \ s rest -> 
  case runParse p s rest of
    Right a -> Right a 
    Left (msg,s',s'') -> ex s msg s' s''

hint str p = withexp p $ \ s msg s' s'' -> Left (msg++str, s, s'')

toEnd :: Parser ()
toEnd = do
  rep $ sat (\_ -> True)
  pure ()


untillEnd p = Parser $ \ s rest ->
  case runParse p s rest of
    Right (a,s,"") -> Right (a,s,"") 
    Right (a,s @ (SourcePos path _ _),rest) -> let
      Right ((),e,"") = runParse toEnd s rest -- depends on the completness of toEnd
      in Left ("incomplete parse", s, e)
    Left e -> Left e 

-- parse one thing, if that works then parse the other thing
(+++) :: Parser a -> Parser b -> Parser (a,b)
pa +++ pb =  do a <- pa; b <- pb; return (a,b)


mapParser :: Parser a -> (a->b) -> Parser b
mapParser pa f = fmap f pa

(^^) = mapParser

-- read in a char (from Hutton)
item :: Parser Char
item = Parser $ \ s@(SourcePos path col row) input -> 
  case input of 
    ""    -> Left ("unexpected empty input", s,s) 
    ('\n':t) -> Right ('\n', SourcePos path (col+1) 0, t)
    (h:t) -> Right (h, SourcePos path col (row+1), t)

-- read in a char if it passes a test, (from Hutton)
sat :: (Char -> Bool) -> Parser Char
sat p = do 
  s <- gets
  c <- item
  if p c
    then pure c
    else failParse' s $ "unexpected char encounted: " ++ [c]


-- parse exactly a string, return that string (in Hutton as the poorly named "string")
literal' :: String -> Parser String
literal' "" = pure ""
literal' (h:t) = do 
  sat (==h)
  literal' t
  pure (h:t)

literal str = hint (" in '"++ str ++"'") $ literal' str

--try to parse a, if that doesn't work try to parse b (slightly different from the Hutton)
(<||>) :: Parser a -> Parser b -> Parser (Either a b)
parserA <||> parserB = Parser $ \ s input ->
  case runParse parserA s input of
    Right (a, s', rest) -> Right (Left a, s', rest) 
    Left _ -> case runParse parserB s input of
      Right (b, s', rest) -> Right (Right b, s', rest)
      Left msg -> Left msg -- differ to the last msg, might want to accumulate the earlier one as a warning

-- like <||> but easier on the same type (from Hutton)
(<|>) :: Parser a -> Parser a -> Parser a
l <|> r = do 
  res <- l <||> r
  case res of
    Left  a -> pure a
    Right a -> pure a

-- take a parser and parse as much as possible into a list, always parse at least 1 thing, (from Hutton)
some :: Parser a -> Parser [a]
some pa = do 
  a <- pa
  rest <- rep pa
  pure (a:rest)

-- take a parser and parse as much as possible into a list, (in Hutton as "many")
rep :: Parser a -> Parser [a]
rep pa = do 
  res <- some pa <||> pure []
  case res of 
    Left ls  -> pure ls
    Right ls -> pure ls


-- parse a digit (from Hutton)
digit :: Parser Char
digit = sat isDigit


-- parse natural numbers, like "123", or "000230000"
natParser :: Parser Integer
natParser = hint " in nat number" $ do 
  digits <- some digit
  pure $ read digits

intParser  :: Parser Integer
intParser = do r <- literal "-" <||> natParser
               case r of
                Left _ -> fmap (0-) natParser
                Right n -> return n

-- parse what we will consider a good variable name
-- TODO: rename to name?  vars are used for all identifier positions
identifierParser :: Parser String
identifierParser = withexp (do 
  head <- sat isAlpha <|> sat (== '_')
  tail <- rep (sat isAlpha <|> digit <|>  sat (=='\''))
  pure $ head : tail) $  \ s msg s' s'' -> Left ("invalid variable", s, s'')

-- use the first working parser
oneOf :: [Parser a] -> Parser a
oneOf [] = error "empty list of alternatives"
oneOf [p] = p
oneOf (pa:rest) = pa <|> oneOf rest


--parse spaces, throw them away
spaces :: Parser ()
spaces = do 
  rep (sat isSpace)
  pure ()
