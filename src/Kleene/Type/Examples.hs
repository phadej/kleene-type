{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}
module Kleene.Type.Examples (
    -- * Nullable
    -- | /Nullable/ regular expression is regular expression which
    -- matches on empty list.
    nullable1,
    nullable2,
    nullable3,
    nullable4,
    nullable5,
    nullable6,

    -- * /Isomorphism/ examples
    -- | 'HList' can be abused for many things:

    -- ** Unit, tuples i.e. products
    unitEx, unitEx', pairEx, pairEx',
    tripleEx, tripleExB, tripleExC,

    -- ** Untagged sum
    untaggedSumEx, untaggedSumEx',

    -- ** Tagged sum
    -- | 'InL' and 'InR' are /keywords/, they act as proxies for themselves.
    InL (..), InR (..), Sum,
    taggedSumEx, taggedSumEx',

    -- ** List
    listEx, listEx',
  ) where

import Kleene.Type

-------------------------------------------------------------------------------
-- Nullable
-------------------------------------------------------------------------------

-- | 'E' is nullable.
nullable1 :: forall xs. MatchI E xs => HList xs -> ()
nullable1 = impl (justMatchIt :: Match E xs) where
    impl = withE ()

-- | @'S' r@ for all @r@ is nullable
nullable2 :: forall xs. MatchI (S (V Bool)) xs => HList xs -> [Bool]
nullable2 = impl (justMatchIt :: Match (S (V Bool)) xs) where
    impl = withStarR (:) [] (withV id)

-- | @r ':\/' s@ is nullable if either @r@ or @s@ is nullable.
nullable3 :: forall xs. MatchI (V Bool \/ E) xs => HList xs -> Maybe Bool
nullable3 = impl (justMatchIt :: Match (V Bool \/ E) xs) where
    impl = withUnion (withV Just) (withE Nothing)

-- | @r ':\/' s@ is nullable if either @r@ or @s@ is nullable.
nullable4 :: forall xs. MatchI (E \/ V Bool) xs => HList xs -> Maybe Bool
nullable4 = impl (justMatchIt :: Match (E \/ V Bool) xs) where
    impl = withUnion (withE Nothing) (withV Just)

-- | @r ':<>' s@ is nullable if both @r@ or @s@ are nullable.
nullable5 :: forall xs. MatchI (E <> E) xs => HList xs -> ()
nullable5 = impl (justMatchIt :: Match (E <> E) xs) where
    impl :: Match (E <> E) xs -> HList xs -> ()
    impl = withAppend (<>) (withE ()) (withE ())

-- | /Complex/ example.
nullable6 :: forall xs. MatchI (E <> E <> S (V Bool)) xs => HList xs -> ()
nullable6 = impl (justMatchIt :: Match (E <> E <> S (V Bool)) xs) where
    impl :: Match (E <> E <> S (V Bool)) xs -> HList xs -> ()
    impl = withAppend
        (<>)
        (withE ())
        (withAppend
            (<>)
            (withE ())
            (withStarMon (withV (const ()))))

-------------------------------------------------------------------------------
-- Examples
-------------------------------------------------------------------------------

-- | Unit
unitEx :: forall xs a. MatchI (V a) xs => HList xs -> a
unitEx  = impl (justMatchIt :: Match (V a) xs) where
    impl :: Match (V a) xs -> HList xs -> a
    impl = withV id

unitEx' :: a -> REList (V a)
unitEx' = REList matchV . hsingleton

-- | Pair
pairEx :: forall xs a b. MatchI (V a <> V b) xs => HList xs -> (a, b)
pairEx = impl (justMatchIt :: Match (V a <> V b) xs) where
    impl :: Match (V a <> V b) xs -> HList xs -> (a, b)
    impl = withAppend (,) (withV id) (withV id)

pairEx' :: (a, b) -> REList (V a <> V b)
pairEx' (x, y) = REList (matchA matchV matchV) (x ::: y ::: Nil)

-- | Triple
tripleEx :: forall xs a b c. MatchI (V a <> V b <> V c) xs => HList xs -> (a, b, c)
tripleEx = impl (justMatchIt :: Match (V a <> V b <> V c) xs) where
    impl :: Match (V a <> V b <> V c) xs -> HList xs -> (a, b, c)
    impl = withAppend (\a (b,c) -> (a,b,c))
        (withV id)
        (withAppend (,) (withV id) (withV id))

-- | Triple, associated other way
tripleExB :: forall xs a b c. MatchI ((V a <> V b) <> V c) xs => HList xs -> (a, b, c)
tripleExB = impl (justMatchIt :: Match ((V a <> V b) <> V c) xs) where
    impl :: Match ((V a <> V b) <> V c) xs -> HList xs -> (a, b, c)
    impl = withAppend (\(a,b) c -> (a,b,c))
        (withAppend (,) (withV id) (withV id))
        (withV id)

tripleExC :: forall xs b c. MatchI ((E <> V b) <> V c) xs => HList xs -> ((), b, c)
tripleExC = impl (justMatchIt :: Match ((E <> V b) <> V c) xs) where
    impl :: Match ((E <> V b) <> V c) xs -> HList xs -> ((), b, c)
    impl = withAppend (\(a,b) c -> (a,b,c))
        (withAppend (,) (withE ()) (withV id))
        (withV id)

untaggedSumEx :: forall xs a b. MatchI (V a \/ V b) xs => HList xs -> Either a b
untaggedSumEx = impl (justMatchIt :: Match (V a \/ V b) xs) where
    impl :: Match (V a \/ V b) xs -> HList xs -> Either a b
    impl = withUnion (withV Left) (withV Right)

untaggedSumEx' :: Either a b -> REList (V a \/ V b)
untaggedSumEx' = either
    (REList (matchL matchV) . hsingleton)
    (REList (matchR matchV) . hsingleton)

data InL = InL deriving (Eq, Show)
data InR = InR deriving (Eq, Show)

-- | Think: 'Either', keywords make match less ambiguous.
type Sum a b = V InL <> V a \/ V InR <> V b

-- | Tagged union: "proper" 'Either'.
taggedSumEx :: forall xs a b. MatchI (Sum a b) xs => HList xs -> Either a b
taggedSumEx = impl (justMatchIt :: Match (Sum a b) xs) where
    impl :: Match (Sum a b) xs -> HList xs -> Either a b
    impl = withUnion
        (withAppend ($) (withV (const Left))  (withV id))
        (withAppend ($) (withV (const Right)) (withV id))

taggedSumEx' :: Either a b -> REList (Sum a b)
taggedSumEx' = either
    (REList (matchL $ matchA matchV matchV) . (InL :::) . hsingleton)
    (REList (matchR $ matchA matchV matchV) . (InR :::) . hsingleton)

-- | List
listEx :: forall xs a. MatchI (S (V a)) xs => HList xs -> [a]
listEx = impl (justMatchIt :: Match (S (V a)) xs) where
    impl :: Match (S (V a)) xs -> HList xs -> [a]
    impl = withStarR (:) [] (withV id)

listEx' :: [a] -> REList (S (V a))
listEx' = foldr f z where
    z :: REList (S (V a))
    z = REList matchN Nil

    f :: a -> REList (S (V a)) -> REList (S (V a))
    f x (REList m xs) = REList (matchC matchV m) (x ::: xs)
