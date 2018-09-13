{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
{-# OPTIONS_GHC -fplugin=KleenePlugin #-}
{-# OPTIONS_GHC -dcore-lint #-}
-- {-# OPTIONS_GHC -fprint-explicit-foralls #-}
module Main where

import Kleene.Type
import Kleene.Type.Examples
import Test.QuickCheck
import Test.QuickCheck.Poly (A, B)

main :: IO ()
main = do
    quickCheck $ isomorphismProp1 @A            unitEx      unitEx'
    quickCheck $ isomorphismProp1 @(A, B)       pairEx      pairEx'
    quickCheck $ isomorphismProp1 @(Either A B) taggedSumEx taggedSumEx'
    quickCheck $ isomorphismProp1 @[A]          listEx      listEx'

    -- works because A and B are different!
    quickCheck $ isomorphismProp1 @(Either A B) untaggedSumEx untaggedSumEx'

  where
    isomorphismProp1
        :: forall a re. (Eq a, Show a, REInductionC Show re)
        => (forall xs. MatchI re xs => HList xs -> a)
        -> (a ->  REList re)
        -> a
        -> Property
    isomorphismProp1 f g x =
        let y :: REList re
            y = g x

            z :: a
            z = withREListI y f

        in counterexample (show y) (x === z)

-------------------------------------------------------------------------------
-- Basic examples
-------------------------------------------------------------------------------

ex1 :: Match ((V Int \/ V Bool) <> V String) xs -> HList xs -> String
ex1 = withAppend (\x y -> x ++ " ~> " ++ y) showIntBool (withV id)
  where
    showIntBool :: Match (V Int \/ V Bool) xs -> HList xs -> String
    showIntBool = withUnion (withV show) (withV show)

ex2 :: Match (S ((V Int \/ V Bool) <> V String)) xs -> HList xs -> String
ex2 = withStarR (\x y -> x ++ " : " ++ y) "End" ex1

-- | >>> usageEx2
-- "1 ~> one : 2 ~> two : True ~> true : End"
usageEx2 :: String
usageEx2 = ex2
    (reInt `matchC` reInt `matchC` reBool `matchC` MatchN)
    ((1 :: Int) ::: "one" ::: (2 :: Int) ::: "two" ::: True ::: "true" ::: Nil)
  where
    reInt :: Match ((V Int \/ V Bool) <> V String) '[Int, String]
    reInt = matchA (MatchL MatchV) MatchV

    reBool :: Match ((V Int \/ V Bool) <> V String) '[Bool, String]
    reBool = matchA (MatchR MatchV) MatchV

-------------------------------------------------------------------------------
-- [[ Nicer, Syntax ]]
-------------------------------------------------------------------------------

syntaxEx :: String
syntaxEx = ex2
    (reInt `matchC` reInt `matchC` reBool `matchC` MatchN)
    [[ 1 :: Int, "one", 2 :: Int, "two", True, "true" ]]
  where
    reInt :: Match ((V Int \/ V Bool) <> V String) '[Int, String]
    reInt = matchA (MatchL MatchV) MatchV

    reBool :: Match ((V Int \/ V Bool) <> V String) '[Bool, String]
    reBool = matchA (MatchR MatchV) MatchV

exHList :: HList '[Int, Bool]
exHList = [[ 1, True ]]

exRList :: REList (S (V Bool))
exRList = ([ False, True ])

exRList2 :: String
exRList2 = (( show :: REList (S (V Bool)) -> String, False, True ))

-------------------------------------------------------------------------------
-- Nullable
-------------------------------------------------------------------------------

usageNullable1 :: ()
usageNullable1 = nullable1 Nil

-- DEMO: Fails, unexpected "character"
-- usageNullable1' :: [Bool]
-- usageNullable1' = nullable1 [[ True ]]

usageNullable2 :: [Bool]
usageNullable2 = nullable2 Nil

usageNullable3 :: Maybe Bool
usageNullable3 = nullable3 Nil

usageNullable4 :: Maybe Bool
usageNullable4 = nullable4 Nil

usageNullable5 :: ()
usageNullable5 = nullable5 Nil

usageNullable6 :: ()
usageNullable6 = nullable6 Nil

-------------------------------------------------------------------------------
-- Isomorphism  examples
-------------------------------------------------------------------------------

usageUnitEx :: a -> a
usageUnitEx x = unitEx [[ x ]]

-- DEMO: Fails, unexpected end-of-input
-- usageUnitEx' :: a -> a
-- usageUnitEx' x = unitEx Nil

usagePairEx :: a -> b -> (a, b)
usagePairEx x y = pairEx [[ x, y ]]

usageTripleEx :: a -> b -> c -> (a, b, c)
usageTripleEx x y z = tripleEx [[ x, y, z ]]

usageTripleExB :: a -> b -> c -> (a, b, c)
usageTripleExB x y z = tripleExB [[ x, y, z ]]

usageTripleExC :: b -> c -> ((), b, c)
usageTripleExC y z = tripleExC [[ y, z ]]

usageUntaggedSumEx1 :: a -> Either a b
usageUntaggedSumEx1 x = untaggedSumEx [[ x ]]

usageUntaggedSumEx2 :: b -> Either a b
usageUntaggedSumEx2 x = untaggedSumEx [[ x ]]

-- DEMO: Fails, ambiguous matches
-- usageUntaggedSumEx3 :: a -> Either a a
-- usageUntaggedSumEx3 x = untaggedSumEx [[ x ]]

usageTaggedSumEx1 :: a -> Either a b
usageTaggedSumEx1 x = taggedSumEx [[ InL, x ]]

usageTaggedSumEx2 :: b -> Either a b
usageTaggedSumEx2 x = taggedSumEx [[ InR, x ]]

usageListEx1 :: [a]
usageListEx1 = listEx Nil

usageListEx2 :: a -> [a]
usageListEx2 x = listEx [[ x ]]

usageListEx3 :: a -> a -> [a]
usageListEx3 x y = listEx [[ x, y ]]

-------------------------------------------------------------------------------
-- Polymorphic examples
-------------------------------------------------------------------------------

listOfInts :: REList (S (V Int))
listOfInts = ([ 1, 2, 3 ])

listOfIntLists :: REList (S (V [Int]))
listOfIntLists = ([ [1], [2, 3] ])

nonAmbg :: (forall a b. REList (V a <> V b <> (V a \/ V b)) -> r) -> r
nonAmbg f = f ([ True, 'a', 'b' ])

-- DEMO: This doesn't match!
-- nonAmbgFail :: (forall a b. REList (V a <> V b <> (V a \/ V b)) -> r) -> r
-- nonAmbgFail f = f ([ True, 'a', "foo" ])

-------------------------------------------------------------------------------
-- TOP
-------------------------------------------------------------------------------

#ifdef KLEENE_TOP

topEverything :: (REList T -> r) -> r
topEverything f = (( f,  'a', True, "foobar" ))

topEmpty :: (REList T  -> r) -> r
topEmpty f = f (mkREList Nil) -- TODO: Allow (( f )) -- syntax

-- DEMO: This doesn't match!
-- add -fprint-explicit-foralls
-- topEverything2 :: (REList (T <> T) -> r) -> r
-- topEverything2 f = (( f,  'a', True, "foobar" ))

-- but this works!
topEmpty2 :: (REList (V Char <> T <> T <> V Int)  -> r) -> r
topEmpty2 f = (( f, 'a', 5 ))
#endif
