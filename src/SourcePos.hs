{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DeriveDataTypeable, DeriveGeneric, MultiParamTypeClasses, FlexibleContexts, FlexibleInstances, DeriveFunctor, RankNTypes, LambdaCase  #-}

module SourcePos where
import Unbound.Generics.LocallyNameless
import GHC.Generics (Generic)
import Data.Typeable (Typeable)
import AlphaShow 


import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

-- TODO shift to https://github.com/github/semantic/tree/master/semantic-source#readme

type Path = String

-- TODO figure out what is going on here and possibly do that https://github.com/sweirich/trellys/blob/63ea89d8fa09929c23504665c55a3d909fe047c5/zombie-trellys/src/Language/Trellys/GenericBind.hs#L44
-- TODO rename char =col
data SourcePos = SourcePos {path::Path, row::Int, char :: Int}
  deriving (
    Show,
   Generic, Typeable)

instance Alpha SourcePos
instance Subst a SourcePos
instance AlphaLShow SourcePos

-- instance Show SourcePos where
--   show = lfullshow

instance Eq SourcePos where
  (==) = aeq

instance Ord SourcePos where
  compare = acompare

debugSR = SourceRange (Just "debug") (SourcePos "" 0 0) (SourcePos "" 0 1)

data SourceRange = SourceRange {source :: Maybe String, start::SourcePos, end::SourcePos}
  deriving (
    -- Show,
   Generic, Typeable)

instance Show SourceRange where
  show (SourceRange {start=start, end=end})= prettyRangeloc start end

instance Alpha SourceRange
instance Subst a SourceRange
instance AlphaLShow SourceRange where
  aShow _ (SourceRange {start=start, end=end}) = pure (Set.empty,prettyRangeloc start end)

-- instance Show SourceRange where
--   show = lfullshow

instance Eq SourceRange where
  (==) = aeq

instance Ord SourceRange where
  compare = acompare


fullRange path s = SourceRange (Just s) (SourcePos path 0 0) (endPos path s)

-- slightly different then how newlines are handled in the parser
endPos :: Path -> String -> SourcePos
endPos path str = SourcePos path (length (lines' str)-1) (length $ last $ lines' str)

lines' str = 
  case lines str of
    [] -> [""]
    x -> x

prettyRange (SourceRange Nothing l r) = -- ["no src"]++
  [prettyRangeloc l r]
prettyRange (SourceRange (Just s) l r) = prettyRange' s l r
  ++ [prettyRangeloc l r]


prettyRange' str s@(SourcePos path col row) s'@(SourcePos path' col' row')
   | path == path' && col==col' && row==row' =
      [lines'  str !! col -- TODO will have line encodeing issues
      ,replicate row ' '  ++ "^"]
prettyRange' str s@(SourcePos path col row) s'@(SourcePos path' col' row')
   | path == path' && col==col' =
      [lines'  str !! col -- TODO will have line encodeing issues
      ,replicate row ' '  ++  replicate (row' - row) '^']
prettyRange' str s@(SourcePos path col row) s'@(SourcePos path' col' row')
   | path == path' = 
     case slice col col' $ lines' str of
       start : (snoc -> (middle, last) ) -> [replicate row ' ' ++ drop row start]  ++ middle ++ [take row' last]
       [] -> ["invalid range: " ++ prettyRangeloc s s']
      --  [] -> error $ "invalid range: " ++ prettyRangeloc s s'
prettyRange' str _ _ =
      ["accross different files"]



prettyRangeloc (SourcePos path col row) (SourcePos path' col' row') 
   | path == path' && col==col' && row==row' =
      path ++ ":" ++ show col ++ "@" ++ show row
prettyRangeloc (SourcePos path col row) (SourcePos path' col' row') 
   | path == path' && col==col'  =
      path ++ ":" ++ show col ++ "@" ++ show row ++ "-" ++ show row'
prettyRangeloc (SourcePos path col row) (SourcePos path' col' row') 
   | path == path'  =
      path ++ ":" ++ show col ++ "@" ++ show row ++ "-" ++ show col' ++ "@" ++ show row'
prettyRangeloc (SourcePos path col row) (SourcePos path' col' row') =
      path ++ ":" ++ show col ++ "@" ++ show row ++ "-" ++ path ++ show col' ++ "@" ++ show row'




-- for webASM codemirror

fullChar :: String -> SourcePos -> Int
fullChar s (SourcePos _ row char) = char + fullChar' (lines' s) row

fullChar' :: [String] -> Int -> Int
fullChar' _ 0 = 0
fullChar' (s:rest) lines | lines > 0  = length s + 1 +  fullChar' rest (lines-1)



--eee = "data Unit : * {\n  | tt  : Unit\n};\n\n\ndata Unit : * {\n  | tt  : Uni\n};\n\n\ndata Unit : * {\n  | tt  : Unit\n};\n"

-- another missind std lib function
slice :: Int -> Int -> [a] -> [a]
slice from to xs = take (to - from + 1) (drop from xs)

snoc :: [a] -> ([a],a)
snoc [a] = ([],a)
snoc (h : (snoc -> (t,l))) = (h:t,l)