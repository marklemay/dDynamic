{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DeriveDataTypeable, DeriveGeneric, MultiParamTypeClasses, FlexibleContexts, FlexibleInstances, DeriveFunctor, RankNTypes, LambdaCase  #-}
--TODO clean up GHC params

module Ast where


import Unbound.Generics.LocallyNameless
import GHC.Generics (Generic)
import Data.Typeable (Typeable)

import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad (guard)

import Data.Monoid (Any(..))
import Control.Applicative (Applicative(..), (<$>))
import Unbound.Generics.LocallyNameless.Internal.Fold (foldMapOf, toListOf)

import UnboundHelper
import AlphaShow 
import SourcePos

import Data.List
import Unbound.Generics.LocallyNameless.Name ( Name(Bn, Fn) )
import Unbound.Generics.LocallyNameless.Bind 
import Unbound.Generics.LocallyNameless.Unsafe (unsafeUnbind)


-- For typelevel documantation
type Term = Exp
type Ty = Exp

type Var = Name Term

-- | type constructor names
type TCName = String

-- | data constructor names
type DCName = String

type RefName = String


data Exp = 
  V Var
  
  | Ref String

  -- | type annotation
  | (:::) Term Ty

  --Terms

  -- standard syntax
  | Fun (Bind (Var {- self -}, Var {- arg -}) Term)
  | App Term Term

  -- user defined
  | DCon DCName -- arguments would be apped
  | Case [Term] (An (Tel Exp (Maybe Ty) Ty)) [Match]

  -- wierd stuff
  | Solve (An Ty) -- TODO: redundant with ty anntoation

  -- Types
  -- standard syntax
  | Pi Ty (Bind Var Ty)

  | TCon TCName

  -- Type in type 
  | TyU

  -- for errormsgs
  | Pos SourcePos Exp SourcePos
  
  deriving (
    -- Show,
   Generic, Typeable)

instance Alpha Exp
instance AlphaLShow Exp

instance Subst Exp Exp where
  -- `isvar` identifies the variable case in your AST.
  isvar (V x) = Just (SubstName x)
  isvar _     = Nothing


-- from https://github.com/sweirich/pi-forall/blob/2014/full/src/Environment.hs for user defined types
  
-- | A 'Match' is a possible branch alternative in a 'Case'
newtype Match = Match (Bind [Pat] Term) deriving (Generic, Typeable)

instance Alpha Match
instance Subst Exp Match
instance AlphaLShow Match
instance Show Match where
  show = lfullshow

data Pat 
  = Pat DCName [Pat]
  | PVar Var
  -- TODO ppos?
  deriving (Generic, Typeable)

instance Alpha Pat
instance Subst Exp Pat -- vacuous substitution
instance AlphaLShow Pat


instance Show Pat where
  show (PVar x) = show x
  show (Pat dCName []) = "(" ++ dCName ++ ")"
  show (Pat dCName args) = "(" ++ dCName ++ " " ++ (concat $ intersperse " " $ show <$> args) ++ ")"

instance Eq Pat where
  (==) = aeq

data DataDef = DataDef (Telescope ()) (Map DCName (Telescope [Term])) deriving (Show, Generic, Typeable, Eq)
-- the [Ty] and [Term] should always be the same length
instance Alpha DataDef
instance Subst Exp DataDef
instance AlphaLShow DataDef


type Telescope = Tel Exp Ty


erasePos (Pos _ e _) = erasePos e
erasePos (e ::: t) = erasePos e ::: erasePos t
erasePos (Fun (B p bod)) = Fun (B p $ erasePos bod)
erasePos (e `App` t) = erasePos e `App` erasePos t
erasePos (Case s ann bs) = 
  Case (erasePos <$> s) ann $ (\ (Match (B p bod)) -> Match (B p $ erasePos bod)) <$> bs 
  -- TODO erase in annotation
erasePos (Pi aTy ((B p bod))) = Pi (erasePos aTy) $ B p $ erasePos bod
-- erasePos (V x) = V x
-- erasePos TyU = TyU
erasePos x = x



-- for indexing into maps, positons are disregarded making this technically unlawful
instance Eq Exp where
  l == r = erasePos l `aeq` erasePos r

-- for indexing into maps
instance Ord Exp where
  l `compare` r = erasePos l `acompare` erasePos r

-- quality of life stuff that only lives here for dumb cyclic import reasons

instance Show Exp where
  -- show e = lfullshow e
  -- show e = codeshow e 
  show e = prettyShow False e 0


-- the code view
--TODO: haskell show typeclass
-- also still bad about vars
codeshow e =
    case simpleNat e of
      Just n -> "(n " ++ show n ++ ")"
      -- Nothing -> case simpleVec e of
      --   Just (ty, ls) -> "(ls " ++ show ls ++ " "  ++ show ty ++ ")"
      --   Nothing ->
      --     case runFreshM $ simpleLam e of
      --       Just e ->  "(lam " ++ codeshow e ++ ")"
      Nothing ->
        case justSimpleFunTy e of
          Just (aty,outTy) ->  "(" ++ codeshow aty ++ " --> "++ codeshow outTy ++ ")"
          Nothing ->
            case e of
              (f `App` a) ->  "(" ++ codeshow f ++ " `App` "++ codeshow a ++ ")"
              (TCon "Nat") ->  "nat"
              (V v) ->  "(V " ++ show v ++ ")"
              (trm ::: ty) ->  "(" ++ codeshow trm ++ " ::: "++ codeshow ty ++ ")"
              
              -- (Fun an bod) ->  "(Fun " ++ codeshow an ++ " "++ codeshow bod ++ ")"
              (DCon dCName) ->  "(DCon \"" ++ dCName ++ "\")"
              -- (Case scrut (An (Just an)) branches) ->  "(Case " ++  codeshow scrut ++ " (ann $"++ bndcodeshow an  ++ ")  "++ "[" ++ (concat $ intersperse ", " (fmap codeshowMatch branches)) ++ "]" ++ ")"
              -- (Solve an) ->  "(Solve " ++  codeshow an ++ ")"
              (Pi aTy outTy) ->  "(Pi " ++ codeshow aTy  ++ " "++ bndcodeshow' outTy ++ ")"
              (TCon tCName) ->  "(TCon \"" ++ tCName  ++ "\")"
              -- (TCon tCName indicies) ->  "(TCon \"" ++ tCName  ++ "\" "++ "[" ++ (concat $ intersperse ", " $ fmap codeshow indicies) ++ "]" ++ ")"
              TyU ->  "TyU"
              Pos s ex e ->  "(Pos "++ show s ++ " " ++  codeshow ex ++ " " ++ show e ++")"
              -- Pos _ e _ ->  "(Pos _ " ++ codeshow e ++ " _)"
              -- Pos _ e _ ->  codeshow e
              e ->  "_"
              -- e ->  "{- " ++ show e ++ "-}"



bndcodeshow :: Bind (Var, [Var]) Ty -> [Char]
bndcodeshow bnde = runFreshM $ do -- TODO this is buggy
  (pat, e) <- unbind bnde
  pure $ " bind " ++ show pat ++ " $ " ++ codeshow e

bndcodeshow' :: Bind Var Ty -> [Char]
bndcodeshow' bnde = runFreshM $ do -- TODO this is buggy
  (pat, e) <- unbind bnde
  pure $ " bind " ++ show pat ++ " $ " ++ codeshow e

-- codeshowMatch :: Match -> [Char]
-- codeshowMatch (Match n bnde) = runFreshM $ do -- TODO this is buggy
--   (pat, e) <- unbind bnde
--   pure $ "Match \"" ++ n ++ "\" $ bind " ++ show pat ++ " $ " ++ codeshow e



-- a hacky show for presentation perposes
-- Ideally should match direct haskell
simpleNat (DCon "Z") =  Just 0
simpleNat (DCon "S" `App` e) = (1 +) <$> simpleNat e
simpleNat _ = Nothing


-- ls [] ty = DCon "Nil" `App` ty
-- ls (h:tl) ty = DCon "Cons" `App` ty  `App` h `App` (n $ fromIntegral $ length tl) `App` (ls tl ty)
simpleVec :: Term -> Maybe (Ty, [Term])
simpleVec (DCon "Nil" `App` ty) =  Just (ty, [])
simpleVec (DCon "Cons" `App` ty `App` h `App` n `App` rest) = do
  (ty', rest') <- simpleVec rest
  n' <- simpleNat n
  guard $ ty `aeq` ty'
  guard $ fromIntegral (length rest') == fromIntegral n'
  Just (ty, h : rest')
simpleVec _ = Nothing

-- justLam :: Term -> Maybe (Bind Var Exp)
justLam :: Term -> Maybe (Var, Exp)
justLam (Fun bndbod@(B (self, x) bod)) = 
  if has' initialCtx (AnyName (Bn 0 0 :: Var)) bod
    then Nothing 
    else 
      let ((_, x), bod) = unsafeUnbind bndbod 
      in Just (x, bod)
justLam _ = Nothing

justSimpleFunTy :: Term -> Maybe (Exp, Exp)
justSimpleFunTy (Pi aTy (bndbodTy@(B x bod))) = 
  if has' initialCtx (AnyName (Bn 0 0 :: Var)) bod
    then Nothing 
    else 
      let (_, bod) = unsafeUnbind bndbodTy 
      in Just (aTy, bod)
justSimpleFunTy _ = Nothing

simpleShow :: Bool -> Exp -> Integer -> String
simpleShow b e = 
  case e of
    V x -> \ _ -> show x
    Ref x -> \ _ -> show x
    TyU -> \ _ -> "*" 
    Solve _ -> \ _ -> "?"
    TCon n -> \ _ -> n
    DCon n -> \ _ -> n
    f `App` a -> paren 8 $ simpleShow b f 8 ++ " " ++ simpleShow b a 9
    Pi aTy (unsafeUnbind-> (x, outTy)) -> paren 2 $ "(" ++ show x ++ " : " ++ simpleShow b aTy 0 ++ ")-> " ++ simpleShow b outTy 2
    Fun (unsafeUnbind-> ((f,x), out)) -> paren 2 $ "fun " ++ show f ++ " " ++ show x ++ " => " ++ simpleShow b out 2
    trm ::: ty -> paren 6 $ simpleShow b trm 7 ++ " : " ++ simpleShow b ty 6
    Case scruts an branches -> 
      paren 8 $  "case " ++ (concat $ intersperse " " $ (\ x -> simpleShow b e 0) <$> scruts) -- simpleShow b scruts 0 -- prob wrong
        ++ case an of
             An Nothing -> ""
             An (Just _) -> 
               "<..>"
            --  An (Just (unsafeUnbind-> ((scrutName, args), ty))) -> 
            --    "<" ++ show scrutName ++ ":_ " ++ (concat $ intersperse " " $ show <$> args) ++ " => " ++ simpleShow b ty 0 ++ ">"
        ++ "{" ++ (concat $ intersperse " " $ 
          fmap (\ (Match (unsafeUnbind-> (args, bod))) -> 
                  "| .." -- ++ dCName ++ " " ++ (concat $ intersperse " " $ show <$>  args) 
                   ++ " => " ++ simpleShow b bod 0 ) branches) 
          ++ "}"
        
    Pos _ e _ -> simpleShow b e
    -- (trm ::: ty) -> paren 6 $ simpleShow b trm 0 ++ " : " ++ simpleShow b ty 0
  where
    paren :: Integer
              -> String
              -> Integer
              -> String
    paren outerLevel showExp curLevel -- TODO sync with other paren function
      | b                     = "(" ++ showExp ++ ")"
      | outerLevel < curLevel = "(" ++ showExp ++ ")"
      | otherwise             =        showExp




tyAscrip :: Exp -> Bool
tyAscrip (_ :::_ ) = True 
tyAscrip (Pos _ e _) = tyAscrip e 
tyAscrip _ = False 

-- b force parens
prettyShow :: Bool -> Exp -> Integer -> String
prettyShow b e = 
  case e of
    V (Fn x _) -> \ _ -> x -- hack for a more pretty view
    V x -> \ _ -> show x
    Ref x -> \ _ -> x
    TyU -> \ _ -> "*" 
    Solve _ -> \ _ -> "?"
    (simpleNat -> Just n) -> \ _ -> show n
    (simpleVec -> Just (ty, ls)) ->  \ _ -> "[" ++ (concat $ intersperse ", " $ ps 0 <$> ls) ++ "]<" ++ ps 0 ty ++ ">"
    TCon n -> \ _ -> n
    DCon n -> \ _ -> n
    f `App` a -> paren 8 $ prettyShow b f 8 ++ " " ++ prettyShow b a 9
    (justSimpleFunTy-> Just (aTy, outTy)) | not $ tyAscrip aTy -> paren 2 $ prettyShow b aTy 3 ++ " -> " ++ prettyShow b outTy 2
    Pi aTy (unsafeUnbind-> (x, outTy)) -> paren 2 $ "(" ++ show x ++ " : " ++ prettyShow b aTy 0 ++ ")-> " ++ prettyShow b outTy 2
    (justLam -> Just (x,out)) -> paren 2 $ "\\ " ++ show x ++ " => " ++ prettyShow b out 2
    Fun (unsafeUnbind-> ((f,x), out)) -> paren 2 $ "fun " ++ show f ++ " " ++ show x ++ " => " ++ prettyShow b out 2
    trm ::: ty -> paren 6 $ prettyShow b trm 7 ++ " : " ++ prettyShow b ty 6
    Case scruts an branches -> 
      paren 8 $  "case " ++ (concat $ intersperse ", " $ ps 0 <$> scruts) --prettyShow b scrut 0 -- prob wrong
        -- ++ case an of
        --      An Nothing -> ""
        --      An (Just (unsafeUnbind-> ((scrutName, args), ty))) -> 
        --        "<" ++ show scrutName ++ ":_ " ++ (concat $ intersperse " " $ show <$> args) ++ " => " ++ prettyShow b ty 0 ++ ">"
        ++ "{" 
        ++ (concat $ intersperse " " $ 
          fmap (\ (Match (unsafeUnbind-> (pats, bod))) -> 
                  "| " ++ (concat $ intersperse " " $ show <$> pats) -- TODO pretty show pats
                   ++ " => " ++ ps 0 bod) branches) 
          ++ "}"
    Pos _ e _ -> prettyShow b e
  where
    ps :: Integer -> Exp -> String -- is this helper clearer or more confusing?
    ps i e = prettyShow b e i
    paren :: Integer
              -> String
              -> Integer
              -> String
    paren outerLevel showExp curLevel -- TODO sync with other paren function
      | b                     = "(" ++ showExp ++ ")"
      | outerLevel < curLevel = "(" ++ showExp ++ ")"
      | otherwise             =        showExp



-- prettyShowWithPos :: Bool -> Exp -> Integer -> (Exp, String)
-- prettyShowWithPos = undefined 

-- data PrintWithPos a = PrintWithPos (String, Integer -> Integer -> a) deriving (Functor) 

-- instance Applicative PrintWithPos where
--   pure a = undefined -- PrintWithPos ("", a)
--   f <*> a = undefined -- _

-- instance Monad PrintWithPos where
--   (>>=) = undefined

-- print :: String -> PrintWithPos ()
-- print = undefined 

-- printPos :: String -> PrintWithPos (Int,Int)
-- printPos = undefined 

-- printe :: String -> Exp -> PrintWithPos Exp
-- printe s e = undefined --PrintWithPos (String ) 


-- prettyShowWithPos' :: Bool -> Exp -> Integer -> PrintWithPos Exp
-- prettyShowWithPos' b e = 
--   case e of
--     V (Fn x _) -> \ _ -> printe x e
--     _ -> undefined 


