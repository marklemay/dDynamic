{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DeriveDataTypeable, DeriveGeneric, MultiParamTypeClasses, FlexibleContexts, FlexibleInstances, DeriveFunctor, RankNTypes, LambdaCase  #-}

module Parser.Exp where



-- import Data.Map (Map)
-- import qualified Data.Map as Map

-- import Data.Set (Set)
-- import qualified Data.Set as Set

-- import Test.Tasty
-- import Unbound.Generics.LocallyNameless
-- import Data.Typeable (Typeable)
-- import GHC.Generics (Generic)


-- import Test.QuickCheck hiding (Fun)
-- import Test.Tasty.QuickCheck (testProperty)

-- import Test.Tasty.HUnit (Assertion(..), assertEqual, assertBool, testCase)

-- import Unbound.Generics.LocallyNameless.Unsafe (unsafeUnbind)
-- import Ast
-- import UnboundHelper
-- import Helper
-- import Env

-- -- import TestHelper
-- import ParserMonad
-- import SourcePos
-- import Parser
-- import Prelude hiding((^^), exp, pi)

-- import Debug.Trace

-- import Parser.Common
-- import StdLib 

-- -- TODO in TestHelper
-- -- right' :: (HasCallStack) => Either [String] b -> IO b
-- -- right' (Left x) = counterexample (unlines x) True
-- -- right' (Right x) = pure x


-- -- TODO (HasCallStack) 
-- x =~= y = counterexample (show x ++ " not alpha equivalent to " ++ show y ++ 
--     "\n" ++ codeshow x ++
--     "\n" ++ codeshow y) (x == y)


-- showParses :: (Exp -> String) -> Exp -> Property
-- showParses sho e = 
--   let se = sho e
--   in case prettyParse "" se exp of -- trace se $ 
--     Left er -> counterexample (unlines er) False
--     Right ee -> 
--       let ee' = undermodule ee mockCtx 
--       in
--        counterexample (
--        "did not parse valid position ranges. printed, " ++ se++
--        "\n" ++ codeshow ee') (validPos ee')
--       .&&.
--       counterexample (
--        "printed, " ++ se++
--        "\n" ++ show e ++ " not alpha equivalent to " ++ show ee ++ 
--        "\n" ++ codeshow e ++
--        "\n" ++ codeshow ee') (e == ee')
--   -- ee <- right' $ prettyParse "" se exp
  
  



-- tests :: TestTree
-- tests =
--   testGroup "parse expressions"
--      [ testProperty "simple fully paren" $ showParses (\e -> simpleShow True e 0)
--       , testProperty "simple min-paren" $ showParses (\e -> simpleShow False e 0)
--       , testProperty "pretty fully paren" $ showParses (\e -> prettyShow True e 0)
--       , testProperty "pretty min-paren" $ showParses (\e -> prettyShow False e 0)
--       -- , testProperty "show instance" $ showParses show -- Turn it on when we have good show
--        ]

-- mockCtx :: DataCtx
-- mockCtx = Map.fromList 
--   [ ("A",DataDef (NoBnd ()) $ Map.singleton "a" (NoBnd []))
--   -- , ("B",DataDef (NoBnd ()) $ Map.singleton "b" (NoBnd []))
--   -- , ("C",DataDef (NoBnd ()) $ Map.singleton "c" (NoBnd []))
--   , ("Nat",DataDef (NoBnd ()) $ Map.fromList 
--     [ ("Z",NoBnd [])
--     , ("S",TelBnd nat $ u $ NoBnd [])])
--   , ("Vec", DataDef (TelBnd TyU $ u $ TelBnd nat $ u $ NoBnd ()) $ Map.fromList [-- length indexed vector, good for examples
--       ("Nil", TelBnd TyU $ bind aTy $ NoBnd [V aTy, n 0]),
--       ("Cons", TelBnd TyU $ bind aTy $ TelBnd (V aTy) $ u $ TelBnd nat $ bind x $ TelBnd (tcon "Vec" [V aTy, V x]) $ u $ NoBnd [V aTy, s $ V x])])
--       -- TODO unfortuantately vanishinly unlikely to hit a well formed vec with len > 1
--   ]
--   where
--     aTy = s2n "aTy"
--     x = s2n "x"

--  -- assume destinct identifiers, 
-- vars = elements $ s2n <$> ["x","y","z"]
-- -- TODO generate from mock?
-- dcNames = elements ["a"
--   -- ,"b"
--   -- ,"c"
--   , "Z", "S"
--   , "Nil", "Cons"
--   ]
-- dCons = DCon <$> dcNames

-- tcNames = elements ["A"
--   -- ,"B"
--   -- ,"C"
--   , "Nat"
--   , "Vec"
--   ]
-- tCons = TCon <$> tcNames



-- splitSize :: Int -> Int -> Gen [Int]
-- splitSize = undefined 
-- -- x <- choose (5, 99999) :: Gen Integer
-- splitSize2 :: Int -> Gen (Int,Int)
-- splitSize2 i = do
--   j <- chooseInt (0, i) 
--   pure (j, i-j)

-- arbitrarySizedMatch :: Int -> Gen Match
-- arbitrarySizedMatch i = do
--   dCon <- dcNames
--   (patSize, bodSize) <- splitSize2 i
--   pat <- vectorOf patSize vars
--   bod <- arbitrarySizedExpr bodSize
--   pure $ Match dCon $ bind pat bod
  
-- arbitrarySizedTel :: Int -> Int -> Int ->  Gen (Tel Exp (Maybe Ty) Ty)
-- arbitrarySizedTel i tuples 0 = do
--   e <- arbitrarySizedExpr (i `div` (tuples+1))
--   pure $ NoBnd e
-- arbitrarySizedTel i tuples j = do
--   x <- vars
--   e <- arbitrarySizedExpr (i `div` (tuples+1))
--   rest <- arbitrarySizedTel i tuples (j-1)
--   elements [TelBnd Nothing $ bind x rest, TelBnd (Just e) $ bind x rest]


-- arbitrarySizedMotive :: Int -> Int -> Gen (An (Tel Exp (Maybe Ty) Ty)) 
-- arbitrarySizedMotive i tuples = do
--   bod <- arbitrarySizedTel i tuples tuples
--   elements [noAn, ann bod]

-- arbitrarySizedCase :: Int -> Int -> Gen Exp
-- arbitrarySizedCase i tuples = do
--   n <- chooseInt (2, i) 
--   scrut <- arbitrarySizedExpr (i `div` n)
--   motive <- arbitrarySizedMotive (i `div` n) tuples
--   branches <- vectorOf (n-2) $ arbitrarySizedMatch (i `div` n)
--   pure $ Case scrut motive branches


-- -- arbitrarySizedList 

-- arbitrarySizedExpr :: Int -> Gen Exp
-- arbitrarySizedExpr i | i < 1 = do 
--   var <- vars
--   dCon <- dCons
--   tCon <- tCons
--   elements [V var, tCon, dCon, TyU, Solve noAn]
-- arbitrarySizedExpr i = do 
--   var <- vars
--   var2 <- vars
--   dCon <- dCons
--   tCon <- tCons
--   rest <- arbitrarySizedExpr (i - 1)
--   e1 <- arbitrarySizedExpr ((i `div` 2) - 1)
--   e2 <- arbitrarySizedExpr (i `div` 2)
--   tuples <- elements [0,1,2,3]
--   cas <- arbitrarySizedCase i tuples
--   elements [
--    e1 ::: e2,
--    e1 `App` e2, Pi e1 $ bind var e2, Fun $ bind (var2, var) rest,
--    cas,
--     V var, tCon, dCon, TyU, Solve noAn]
  

-- instance Arbitrary Exp where
--   arbitrary = sized arbitrarySizedExpr

--   shrink = fullShrink shrink shrink

-- instance (Arbitrary Var) where
--   arbitrary = vars

-- instance (Arbitrary Match) where
--   arbitrary = sized arbitrarySizedMatch

--   shrink (Match bndBod) = Match <$> shrink bndBod

-- instance (Alpha p, Alpha b, Arbitrary p, Arbitrary b) => Arbitrary (Bind p b) where
--   arbitrary = bind <$> arbitrary <*>  arbitrary

--   shrink (unsafeUnbind-> (p, b)) = [bind p' b' | (p',b') <- shrink (p, b)]
