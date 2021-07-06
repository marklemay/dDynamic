{-# LANGUAGE DeriveGeneric, DefaultSignatures, FlexibleInstances, FlexibleContexts, TypeOperators, MultiParamTypeClasses, AllowAmbiguousTypes #-}

module AlphaShow (AlphaLShow, aShow, lfullshow) where -- TODO: push up to unbound generics

import GHC.Generics
import Unbound.Generics.LocallyNameless
import Data.Typeable (Typeable)

import Data.List

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Unbound.Generics.LocallyNameless.Internal.Fold (foldMapOf, toListOf)

{-
type Var = Name Ingredient

data Ingredient
  = Flour
  -- | (:~~:) Ingredient Ingredient
  | Sugar Bool  -- Bool Bool Bool
  | Sugar2 Bool Bool Bool Bool Bool
  | V Var
  | More Ingredient
  | LLL [Ingredient]
  | Lam (Bind Var Ingredient)
  | Lam2 (Bind (Var, Var) Ingredient)
  | Yolo (Bind [Var] Ingredient)
  | App Ingredient Ingredient
  | UhHO String
  deriving (Generic)


instance Alpha Ingredient
instance AlphaLShow Ingredient
  
instance Show Ingredient where
  show = lfullshow -- probly do it via precidence

-}

lfullshow :: AlphaLShow a => a -> String
lfullshow x =
  let 
    freevars = Set.fromList $ toListOf fvAny x
    (vars, str) = runLFreshM $ avoid (Set.toList freevars) $ aShow 0 x
  in case Set.toList freevars ++ Set.toList vars of
       [] -> str
       [v] -> "let " ++ show v ++ "=s2n\""++ show v ++"\" in " ++ str
       ls -> "let (" ++ concat (intersperse "," $ show <$> ls) ++ ") = ("++ concat ((intersperse "," $ (\x -> "s2n\"" ++show x ++ "\"") <$> ls)) ++") in " ++ str
    --  else "let ..." ++ fmap show vars = 
-- (xx,yy) = ("x","y")

class Alpha a => AlphaLShow a where
  aShow :: Int -> a -> LFreshM (Set AnyName, String)
  default aShow :: (Generic a, GAlphaLShow (Rep a)) => Int -> a -> LFreshM (Set AnyName, String)
  aShow i a = gAShow i $ from a

showConst c = pure (Set.empty, show c)

instance AlphaLShow Bool where
  aShow _ = showConst

instance AlphaLShow Char where
  aShow _ = showConst

instance AlphaLShow Integer where
  aShow _ = showConst

instance AlphaLShow Int where
  aShow _ = showConst

instance {-# OVERLAPPING  #-}  AlphaLShow String where
  aShow _ = showConst

instance (Typeable n) => AlphaLShow (Name n) where
  aShow _ = showConst

instance (AlphaLShow a) => AlphaLShow (Ignore a) where
  aShow i ig = do
    (vs,ig') <- aShow appPrec ig
    pure (vs, showParenthises (i >= appPrec) $ "ignoe " ++ ig')

instance (AlphaLShow a, AlphaLShow p) => AlphaLShow (Bind p a) where
  aShow i bnda = do
    (vs,arg,bod) <- lunbind bnda (\ (p,b) -> do (pv, ps) <- aShow appPrec p; (bv, bs) <- aShow appPrec b; pure (bv `Set.union` pv `Set.union` (Set.fromList $ toListOf fvAny p), ps, bs) )
    pure (vs, showParenthises (i >= appPrec) $ "bind " ++ arg ++ " " ++ bod)


instance AlphaLShow a => AlphaLShow (Maybe a)
instance AlphaLShow ()
instance (AlphaLShow a, AlphaLShow b) => AlphaLShow (Either a b)
instance (AlphaLShow a, AlphaLShow b) => AlphaLShow (a,b) where
  aShow i (a,b) = do
    (vars1, str1) <- aShow 0 a
    (vars, str) <- aShow 0 b
    pure (vars1 `Set.union` vars, "("++ str1 ++ ", " ++str ++")")

instance (AlphaLShow a, AlphaLShow b, AlphaLShow c) => AlphaLShow (a,b,c) where
  aShow i (a,b,c) = do
    (vars1, str1) <- aShow 0 a
    (vars2, str2) <- aShow 0 b
    (vars3, str3) <- aShow 0 c
    pure (vars1 `Set.union` vars2 `Set.union` vars3, "("++ str1 ++ ", " ++str2 ++ ", " ++str3 ++")")
-- instance (AlphaShow a, AlphaShow b,AlphaShow c, AlphaShow d) => AlphaShow (a,b,c,d)
-- instance (AlphaShow a, AlphaShow b,AlphaShow c, AlphaShow d, AlphaShow e) =>
--    AlphaShow (a,b,c,d,e)

instance (AlphaLShow a) => AlphaLShow [a] where
  aShow i ls = do
    (vs,str) <- ss ls 
    pure (vs, "["++ str ++"]")

ss [] = pure (Set.empty, "")
ss [a] = do
    (vars, str) <- aShow 0 a
    pure (vars, str)
ss (a:b) = do
    (vars1, str1) <- aShow 0 a
    (vars, str) <- ss b
    pure (vars1 `Set.union` vars, str1 ++ ", " ++ str)



class GAlphaLShow f where
  gAShow :: Int -> f a -> LFreshM (Set AnyName, String)

  isNullary   :: f a -> Bool
  -- -- isNullary = error "generic show (isNullary): unnecessary case"
  isNullary _ = False



instance (GAlphaLShow f, Constructor c) => GAlphaLShow (M1 C c f) where
  gAShow i c@(M1 f) =
    case (conFixity c,  isNullary f) of 
      (Prefix , True)  -> pure (Set.empty, conName c)
      (Prefix , False)  -> do (vars, str) <- gAShow appPrec f; pure (vars, showParenthises (i >= appPrec) $ conName c ++ " " ++ str)
      (Infix _ _ , _)  -> error "Infix is currently broke"
  {-# INLINE gAShow #-}

    -- case (conFixity c,  gAShow appPrec f) of 
    --   (Prefix , [])  -> [pure ([], conName c)]
    --   (Prefix , ls)  -> [do (vars, str) <- flatten ls " "; pure (vars, showParenthises (i >= appPrec) $ conName c ++ " " ++ str) ]

  -- TODO incorrect precidence
      -- (Infix LeftAssociative m, [l, r])  -> [do (vars, str) <- l; (varsr, strr) <- r; pure (vars ++ varsr, showParenthises (i >= m) $ str ++ " " ++conName c ++ " " ++ strr) ]
      -- (Infix RightAssociative m , _, _)  -> undefined
      -- (Infix NotAssociative	 m , _, _)  -> undefined



instance (GAlphaLShow f, Selector s) => GAlphaLShow (M1 S s f) where
  gAShow i (M1 f) = gAShow i f
  {-# INLINE gAShow #-}

instance (GAlphaLShow f) => GAlphaLShow (M1 D d f) where
  gAShow i (M1 f) = gAShow i f
  {-# INLINE gAShow #-}
  
instance (AlphaLShow c) => GAlphaLShow (K1 i c) where
  gAShow i (K1 c) = aShow i c
  {-# INLINE gAShow #-}

instance GAlphaLShow U1 where
  gAShow _ U1 = pure (Set.empty, "")
  {-# INLINE gAShow #-}

  isNullary _ = True
  

instance (GAlphaLShow f, GAlphaLShow g) => GAlphaLShow (f :+: g) where
  gAShow i (L1 f) = gAShow i f
  gAShow i (R1 g) = gAShow i g


instance (GAlphaLShow f, GAlphaLShow g) => GAlphaLShow (f :*: g) where
  gAShow i (f :*: g) = do 
    (vars , str ) <- gAShow appPrec f
    (vars2, str2) <- gAShow appPrec g
    pure (vars `Set.union` vars2, showParenthises (i > appPrec) $ str ++ " " ++ str2)



appPrec :: Int
appPrec = 2


showParenthises :: Bool -> String -> String
showParenthises True s = "(" ++ s ++ ")"
showParenthises false s = s

{-
x, y :: Var
x = s2n "x"
y = s2n "y"

ee = lfullshow $ [bind x (bind y x,y)]


e0 = lfullshow Flour
e1 = lfullshow $ Sugar True
e11 = lfullshow $ Sugar2 True True True True True
-- e12 = fullshow $ Sugar2 True True True True True :~~: Sugar2 True True True True True
e3 = lfullshow $ V $ s2n "x"
e4 = lfullshow $ More $ V $ s2n "x"
e5 = Lam $ bind x $ V $ x
e6 = Lam $ bind x $ Lam $ bind x $ V $ x
e7 = Lam $ bind x $ Lam $ bind y $ V $ y
e8 = Lam2 $ bind (x,y) $ Lam $ bind y $ V $ y
e9 = Yolo $ bind [x,y,y] $ Lam $ bind x $ V $ y
e10 = UhHO "oghhhhhnooooo"
e22 = Lam2 $ bind (x,y) $ V x `App` V y --LLL [V x, V y]
-- e22 = Lam2 $ bind (x,y) $  V y

-- -- Fun $ bind (f,x) $ V f `App` V x

-- -- e8 = let (x,x1) = (s2n"x",s2n"x1") in Lam(bind x $ Lam(bind x1 $ V x1))



-- refs
-- https://github.com/dreixel/generic-deriving/blob/master/src/Generics/Deriving/Show.hs
-- https://www.stephendiehl.com/posts/generics.html
-- https://github.com/lambdageek/unbound-generics/blob/master/src/Unbound/Generics/LocallyNameless/Alpha.hs


-- TODO:

-- precidence could be better
-- could tighten up var name choices a little more (deprioitze unused names)
-- make sure names that are not haskell idenifiers are ok
-- the bind type now has a dumb looking show, possible to override?
-- unbound vars are not letted... this seems ok

-- clean up the monad
-- better name representations
-- more "primative data"
-- patterns
-- keep track of var sorts?
-- records?
-- minimize var names
-- inline it all
-- infix (WIERDER THEN EXPECTED: https://gitlab.haskell.org/ghc/ghc/-/commit/852b603029a047609a54453b1f9cd65035a43afe)
-- precidence 
-- pull request
-- genralize to any monad?
-- shorthands
-- parsing?


-- data BADD =
--   (:++++:) Int Int
--   deriving (Show)

-}