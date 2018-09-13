{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
-- | Regular expression as types.
module Kleene.Type (
    -- * Regular expressions
    RE (..),
    -- ** Tickless aliases
    E, V, S, type (<>), type (\/),

    -- * Heterogenous list
    HList (..),
    hsingleton,
    hlength,

    -- ** Append and Split
    Append,
    append,
    split,
    SList (..),
    SListI (..),
    hlistToSList,

    -- * Match
    Match (..),

    -- ** Implicit match
    MatchI (..),

    -- ** Smart constructors
    matchE, matchV, matchA, matchL, matchR, matchN, matchC,

    -- ** Smart destructors
    withE, withV, withUnion, withAppend, withStarMon, withStarR,

    withAppend3,

    -- * RE-indexed list
    REList (..),
    mkREList,
    withREList,
    withREListI,

    -- * Inductions
    -- | There are two ways to write induction,
    --
    -- *   Using a structure proof, like 'SList'.
    --     If we fold over 'HList', we could use it as a structure proof too;
    --     but for constucting it, we'd need 'SList'.
    --     This is 'listInductionP.
    --
    --     The benefit of this approach is its simplicity.
    --     However, the drawback is that we need to define an auxiliary
    --     type family to provide constrained version.
    --     See @All@ in @generics-sop@ package (version 0.3).
    --
    -- *   Alternatively, we can define a type class directly
    --     parametrised by the type-level structure.
    --
    --     This way additional constraints for different /constructors/
    --     can be added naturally. See 'ListInducton' and 'ListInductionC'.

    -- ** List structure
    ListInduction (..),
    ListInductionC (..),
    listInductionP,

    -- ** RE structure
    REInductionC (..),
    reInductionP,

    -- * Conversion to /Haskelly/ types.
    haskelly,
    Haskelly,

    -- * Key
    Key (..),
    key,
    keyVal,

#ifdef MIN_VERSION_lens
    -- * Lenses
    -- | Naming convention is simple: @r@ + 3-5 characters.
    rval,
    rpair,
    rfst,
    rsnd,
    rsum,
    rleft,
    rright,
    rstar,
    rnil,
    rcons,
#endif

#ifdef KLEENE_TOP
    -- * Top
    T,
    matchT,
    withTop,
#endif

  ) where

-- Needed for the implementation of 'withREList'.
import Data.Proxy           (Proxy (..))
import GHC.Exts             (Constraint)
import GHC.OverloadedLabels (IsLabel (..))
import GHC.TypeLits         (KnownSymbol, Symbol, symbolVal)
import Unsafe.Coerce        (unsafeCoerce)

#ifdef MIN_VERSION_lens
import Control.Lens
       (AsEmpty (..), Cons (..), Iso, Lens, Prism, Prism', Traversal, iso,
       prism, prism', _1, _2, _Left, _Right)
#endif

#ifdef KLEENE_TOP
#define KLEENE_ARGS e v a l r n c t
#define KLEENE_UNARGS _
#else
#define KLEENE_ARGS e v a l r n c
#define KLEENE_UNARGS
#endif

-------------------------------------------------------------------------------
-- Regular expressions
-------------------------------------------------------------------------------

-- | Regular expressions.
data RE a
    = E              -- ^ empty string
    | V a            -- ^ variable
    | RE a :<> RE a  -- ^ append
    | RE a :\/ RE a  -- ^ alternative
    | S (RE a)       -- ^ star
#ifdef KLEENE_TOP
    | T              -- ^ top
#endif

infixr 5 :<>, <>
infixr 4 :\/, \/

type E = 'E
type V = 'V
type S = 'S
type a <> b = a ':<> b
type a \/ b = a ':\/ b
#ifdef KLEENE_TOP
type T = 'T
#endif

-------------------------------------------------------------------------------
-- Heterogenous list
-------------------------------------------------------------------------------

-- | Heterogenous list
data HList :: [*] -> * where
    Nil   :: HList '[]
    (:::) :: x -> HList xs -> HList (x ': xs)

infixr 5 :::

-- | Create singleton 'HList'.
hsingleton :: a -> HList '[a]
hsingleton x = x ::: Nil

instance ListInductionC Show xs => Show (HList xs) where
    showsPrec = unShowList $ listInductionC (Proxy :: Proxy Show)
        (ShowList $ \_ Nil -> showString "Nil")
        (\rec -> ShowList $ \d (x ::: xs) -> f (unShowList rec) d x xs)
      where
        f :: Show y => (Int -> HList ys -> ShowS) -> Int -> y -> HList ys -> ShowS
        f rec d x xs = showParen (d > 5)
            $ showsPrec 6 x
            . showString " ::: "
            . rec 5 xs

-- | Used for both @'Show' ('SList' xs)@ and @'Show' ('HList' xs)@.
newtype ShowList f xs = ShowList { unShowList :: Int -> f xs -> ShowS }

-------------------------------------------------------------------------------
-- HList Append and Split
-------------------------------------------------------------------------------

-- | Type list's shape singleton. Needed for 'split'.
data SList :: [*] -> * where
    SNil  :: SList '[]
    SCons :: forall x xs. SList xs -> SList (x ': xs)

instance ListInduction xs => Show (SList xs) where
    showsPrec = unShowList $ listInduction
        (ShowList $ \_ SNil -> showString "SNil")
        $ \(ShowList rec) -> ShowList $ \d (SCons s) -> showParen (d > 10)
            $ showString "SCons "
            . rec 11 s

-- | Make compiler create 'SList's.
class                 SListI (xs :: [*]) where slistI :: SList xs
instance              SListI '[]         where slistI = SNil
instance SListI xs => SListI (x ': xs)   where slistI = SCons slistI

type family Append (xs :: [*]) (ys :: [*]) :: [*] where
    Append '[]       ys = ys
    Append (x ': xs) ys = x ': Append xs ys

-- | '++' for 'HList's.
append :: HList xs -> HList ys -> HList (Append xs ys)
append Nil        ys = ys
append (x ::: xs) ys = x ::: append xs ys

-- | 'splitAt' for 'HList's. We don't need 'Int', instead we need @'SList' xs@.
split :: SList xs -> HList (Append xs ys) -> (HList xs, HList ys)
split SNil      zs         = (Nil, zs)
split (SCons s) (x ::: zs) = (x ::: xs, ys) where
    ~(xs, ys) = split s zs

-- | Convert 'HList' to 'SList'.
hlistToSList :: HList xs -> SList xs
hlistToSList Nil       = SNil
hlistToSList (_ ::: h) = SCons (hlistToSList h)

hlength :: HList xs -> Int
hlength = acc 0 where
    acc :: Int -> HList xs -> Int
    acc !n Nil        = n
    acc !n (_ ::: xs) = acc (n + 1) xs

-------------------------------------------------------------------------------
-- Match
-------------------------------------------------------------------------------

-- | Proof of match.
--
-- @forall@'s are required, to better document the argument order for
-- Core-term construction in the plugin.
data Match :: RE * -> [*] -> * where
    MatchE :: Match E '[]
    MatchV :: forall a. Match (V a) '[a]
    MatchA :: forall re re' xs ys. SList xs -> Match re xs -> Match re' ys -> Match (re <> re') (Append xs ys)
    MatchL :: forall re re' xs. Match re xs  -> Match (re \/ re') xs
    MatchR :: forall re re' xs. Match re' xs -> Match (re \/ re') xs
    MatchN :: forall re. Match (S re) '[]
    MatchC :: forall re xs ys. SList xs -> Match re xs -> Match (S re) ys -> Match (S re) (Append xs ys)
#ifdef KLEENE_TOP
    MatchT :: forall xs. SList xs -> Match T xs
#endif

infixr 5 `MatchC`, `matchC`

instance Show (Match re xs) where
    showsPrec _ MatchE          = showString "matchE"
    showsPrec _ MatchV          = showString "matchV"
    showsPrec d (MatchA _ p q)  = showParen (d > 10)
        $ showString "matchC "
        . showsPrec 11 p
        . showChar ' '
        . showsPrec 11 q
    showsPrec d (MatchL p)      = showParen (d > 10)
        $ showString "matchL "
        . showsPrec 11 p
    showsPrec d (MatchR p)      = showParen (d > 10)
        $ showString "matchR "
        . showsPrec 11 p
    showsPrec _ MatchN          = showString "matchN"
    showsPrec d (MatchC _ p q)  = showParen (d > 10)
        $ showString "matchC "
        . showsPrec 11 p
        . showChar ' '
        . showsPrec 11 q
#ifdef KLEENE_TOP
    showsPrec _ (MatchT _)      = showString "matchT"
#endif

-------------------------------------------------------------------------------
-- Class
-------------------------------------------------------------------------------

-- | This class has no defined instances.
--
-- "KleenePlugin" can solve the constraints for you.
class MatchI (re :: RE *) (xs :: [*]) where
    justMatchIt :: Match re xs

{-
-- Fake instances
instance MatchI ('S re) '[] where
    justMatchIt = PN

instance MatchI ('S ('V x)) xs => MatchI ('S ('V x)) (x ': xs) where
    justMatchIt = PC PV justMatch
-}

-------------------------------------------------------------------------------
-- Smart constructors
-------------------------------------------------------------------------------

matchE :: Match E '[]
matchE = MatchE

matchV :: Match (V a) '[a]
matchV = MatchV

matchA :: SListI xs => Match r xs -> Match s ys -> Match (r <> s) (Append xs ys)
matchA = MatchA slistI

matchL :: Match r xs -> Match (r \/ s) xs
matchL = MatchL

matchR :: Match s xs -> Match (r \/ s) xs
matchR = MatchR

matchN :: Match (S re) '[]
matchN = MatchN

matchC :: SListI xs => Match r xs -> Match (S r) ys -> Match (S r) (Append xs ys)
matchC = MatchC slistI

#ifdef KLEENE_TOP
matchT :: SListI xs => Match T xs
matchT = MatchT slistI
#endif

-------------------------------------------------------------------------------
-- Smart destructors
-------------------------------------------------------------------------------

-- | Like 'runIdentity' for @'V' a@
withV
    :: (a -> x)
    -> Match (V a) xs -> HList xs
    -> x
withV f MatchV (a ::: Nil) = f a

-- | We /usually/ don't bother eliminate '()'.
withE
    :: x
    -> Match E xs -> HList xs
    -> x
withE x MatchE Nil = x

-- | Like 'either' for @r ':\/' s@.
withUnion
    :: (Match r  xs -> HList xs -> x)
    -> (Match r' xs -> HList xs -> x)
    -> Match (r \/ r') xs -> HList xs
    -> x
withUnion l _ (MatchL re)  = l re
withUnion _ r (MatchR re)  = r re

-- | Like 'uncurry' for @r ':<>' s@.
withAppend
    :: (x -> y -> z)
    -> (forall xs. Match r xs -> HList xs -> x)  -- ^ fst
    -> (forall ys. Match r' ys -> HList ys -> y) -- ^ snd
    -> Match (r <> r') zs -> HList zs
    -> z
withAppend h f g (MatchA s x y) np = case split s np of
    (l, r) -> f x l `h` g y r

withAppend3
    :: (x -> y -> z -> w)
    -> (forall xs. Match r0 xs -> HList xs -> x)  -- ^ fst
    -> (forall ys. Match r1 ys -> HList ys -> y) -- ^ snd
    -> (forall zs. Match r2 zs -> HList zs -> z) -- ^ snd
    -> Match (r0 <> r1 <> r2) ws -> HList ws
    -> w
withAppend3 r f g h = withAppend (\x (y,z) -> r x y z) f (withAppend (,) g h)

-- | Like 'foldMap' for @'S' r@.
withStarMon
    :: forall x r zs. Monoid x
    => (forall xs. Match r xs -> HList xs -> x)  -- ^ to 'Monoid'.
    -> Match (S r) zs -> HList zs
    -> x
withStarMon k = go where
    go :: forall ys. Match ('S r) ys -> HList ys -> x
    go MatchN       Nil = mempty
    go (MatchC s h t) zs  = case split s zs of
        (xs, ys) -> mappend (k h xs) (go t ys)

-- | Like @'foldr' f z@ for @'S' r@.
withStarR
    :: forall x y r zs.
       (x -> y -> y) -- ^ cons
    -> y             -- ^ nil
    -> (forall xs. Match r xs -> HList xs -> x)
    -> Match (S r) zs -> HList zs
    -> y
withStarR f z v = go where
    go :: forall ys. Match ('S r) ys -> HList ys -> y
    go MatchN       Nil = z
    go (MatchC s h t) zs  = case split s zs of
        (xs, ys) -> f (v h xs) (go t ys)

#ifdef KLEENE_TOP
withTop
    :: y
    -> Match T zs -> HList zs
    -> y
withTop = undefined
#endif

-------------------------------------------------------------------------------
-- REList
-------------------------------------------------------------------------------

-- | 'RE'-indexed list.
data REList :: RE * -> * where
    REList :: Match re xs -> HList xs -> REList re

instance REInductionC Show re => Show (REList re) where
    showsPrec d (REList m xs) = showParen (d > 10)
        $ showString "REList "
        . showsPrec 11 m
        . showChar ' '
        . go 11 strings
      where
        strings = unAux (showElements m) xs

        -- We are "showing" HList
        go :: Int -> [Int -> ShowS] -> ShowS
        go _ []       = showString "Nil"
        go b (f : fs) = showParen (b > 5)
            $ f 6
            . showString " ::: "
            . go 5 fs

showElements :: REInductionC Show re => Match re zs -> Aux zs
showElements = reInductionC (Proxy :: Proxy Show) KLEENE_ARGS where
    e :: Aux '[]
    e = Aux $ \Nil -> []

    v :: Show x => Aux '[x]
    v = Aux $ \(x ::: Nil) -> [flip showsPrec x]

    a :: SList xs -> Aux xs -> Aux ys -> Aux (Append xs ys)
    a xs' f g = Aux $ \zs -> case split xs' zs of
        (xs, ys) -> unAux f xs ++ unAux g ys

    l :: Aux xs -> Aux xs
    l = id

    r :: Aux xs -> Aux xs
    r = id

    n :: Aux '[]
    n = e

    c :: SList xs -> Aux xs -> Aux ys -> Aux (Append xs ys)
    c = a

#ifdef KLEENE_TOP
    t :: SList xs -> Aux xs
    t = listInductionP (Aux $ \Nil -> []) $ \(Aux f) -> Aux $ \(_ ::: xs) ->
        const (showChar '?') : f xs
#endif


-- | We could use @ HList xs -> NP (K (Int -> ShowS) xs@,
-- but just using lists we save us defining NP.
newtype Aux xs = Aux { unAux :: HList xs -> [Int -> ShowS] }

-- | Smart-constructor using 'MatchI' constraint.
--
-- /Note:/ The 'REList' uses 'Match', not 'MatchI' as working with
-- expicit 'Match' is more expressive.
-- At least until "KleenePlugin" can solve all possible 'MatchI' constraints.
--
mkREList :: MatchI re xs => HList xs -> REList re
mkREList = REList justMatchIt

-- | >>> withREListI (REList matchV $ hsingleton True) $ withV not justMatchIt
-- False
withREList :: forall re x. REList re -> (forall xs. Match re xs -> HList xs -> x) -> x
withREList (REList m xs) f = f m xs

-- | >>> withREListI (REList matchV $ hsingleton True) $ withV not justMatchIt
-- False
withREListI :: forall re x. REList re -> (forall xs. MatchI re xs => HList xs -> x) -> x
withREListI (REList m xs) f = unsafeCoerce (Magic f :: Magic re x) m xs

-- Same trick as in the @reflection@ package.
newtype Magic re x = Magic (forall xs. MatchI re xs => HList xs -> x)

-------------------------------------------------------------------------------
-- List induction
-------------------------------------------------------------------------------

-- | (Type-level) list induction.
class ListInduction (xs :: [*]) where
    listInduction
        :: f '[]                                -- ^ case: 'SNil'
        -> (forall y ys. f ys -> f (y ': ys))   -- ^ case: 'SCons'
        -> f xs

instance ListInduction '[] where
    listInduction z _ = z

instance ListInduction xs => ListInduction (x ': xs) where
    listInduction z f = f (listInduction z f)

-- | Constrained 'ListInduction'.
class ListInductionC (c :: * -> Constraint) (xs :: [*]) where
    listInductionC
        :: Proxy c
        -> f '[]                                      -- ^ case: 'SNil'
        -> (forall y ys. c y => f ys -> f (y ': ys))  -- ^ case: 'SCons'
        -> f xs

instance ListInductionC c '[] where
    listInductionC _ z _ = z

instance (c x, ListInductionC c xs) => ListInductionC c (x ': xs) where
    listInductionC p z f = f (listInductionC p z f)

-- | This is the third variant of list induction, using a /proof object/ 'SList'.
listInductionP
    :: forall f xs. f '[]                  -- ^ case: 'SNil'
    -> (forall y ys. f ys -> f (y ': ys))  -- ^ case: 'SCons'
    -> SList xs
    -> f xs
listInductionP z f = go where
    go :: SList ys -> f ys
    go SNil      = z
    go (SCons s) = f (go s)

-------------------------------------------------------------------------------
-- RE induction
-------------------------------------------------------------------------------

-- | Induction using 'Match'.
reInductionP
    :: forall f re zs.
       f '[]                                                        -- ^ case: 'MatchE'
    -> (forall x. f '[x])                                           -- ^ case: 'MatchV'
    -> (forall xs ys. SList xs -> f xs -> f ys -> f (Append xs ys)) -- ^ case: 'MatchA'
    -> (forall xs. f xs -> f xs)                                    -- ^ case: 'MatchL'
    -> (forall xs. f xs -> f xs)                                    -- ^ case: 'MatchR'
    -> f '[]                                                        -- ^ case: 'MatchN'
    -> (forall xs ys. SList xs -> f xs -> f ys -> f (Append xs ys)) -- ^ case: 'MatchC'
#ifdef KLEENE_TOP
    -> (forall xs. SList xs -> f xs)                                -- ^ case: 'MatchT'
#endif
    -> Match re zs                                                  -- ^ 'Match' proof
    -> f zs
reInductionP KLEENE_ARGS = go where
    go :: Match (se :: RE *) ys -> f ys
    go MatchE          = e
    go MatchV          = v
    go (MatchA xs p q) = a xs (go p) (go q)
    go (MatchL p)      = l (go p)
    go (MatchR p)      = r (go p)
    go MatchN          = n
    go (MatchC xs p q) = c xs (go p) (go q)
#ifdef KLEENE_TOP
    go (MatchT xs)     = t xs
#endif

-- | Constrainted 'RE' induction of lists!
--
-- We need the 'Match' object, as it connects @re@ and @xs@.
--
-- /Note:/ This is an induction on the structure of the 'Match', not the @xs@ list.
class REInductionC (c :: * -> Constraint) (re :: RE *) where
    reInductionC
        :: Proxy c
        -> f '[]                                                        -- ^ case: 'MatchE'
        -> (forall x. c x =>  f '[x])                                   -- ^ case: 'MatchV'
        -> (forall xs ys. SList xs -> f xs -> f ys -> f (Append xs ys)) -- ^ case: 'MatchA'
        -> (forall xs. f xs -> f xs)                                    -- ^ case: 'MatchL'
        -> (forall xs. f xs -> f xs)                                    -- ^ case: 'MatchR'
        -> f '[]                                                        -- ^ case: 'MatchN'
        -> (forall xs ys. SList xs -> f xs -> f ys -> f (Append xs ys)) -- ^ case: 'MatchC'
#ifdef KLEENE_TOP
        -> (forall xs. SList xs -> f xs)                                -- ^ case: 'MatchT'
#endif
        -> Match re zs                                                  -- ^ 'Match' proof
        -> f zs

instance REInductionC c E where
    reInductionC _ e _ _ _ _ _ _ KLEENE_UNARGS MatchE = e

instance c x => REInductionC c (V x) where
    reInductionC _ _ v _ _ _ _ _ KLEENE_UNARGS MatchV = v

instance (REInductionC c r, REInductionC c s) => REInductionC c (r ':<> s) where
    reInductionC z KLEENE_ARGS (MatchA xs p q) =
        a xs (reInductionC z KLEENE_ARGS p) (reInductionC z KLEENE_ARGS q)

instance (REInductionC c r, REInductionC c s) => REInductionC c (r ':\/ s) where
    reInductionC z KLEENE_ARGS (MatchL p) =
        l (reInductionC z KLEENE_ARGS p)
    reInductionC z KLEENE_ARGS (MatchR p) =
        r (reInductionC z KLEENE_ARGS p)

instance REInductionC c x => REInductionC c (S x) where
    reInductionC _ _ _ _ _ _ n _ KLEENE_UNARGS MatchN          = n
    reInductionC z KLEENE_ARGS (MatchC xs p q) =
        c xs (reInductionC z KLEENE_ARGS p) (reInductionC z KLEENE_ARGS q)

#ifdef KLEENE_TOP
instance REInductionC c T where
    reInductionC _ _ _ _ _ _ _ _ t (MatchT xs) = t xs
#endif

-------------------------------------------------------------------------------
-- Conversion to Haskell types
-------------------------------------------------------------------------------

type family Haskelly (re :: RE *) :: * where
    Haskelly 'E         = ()
    Haskelly ('V a)     = a
    Haskelly (a ':<> b) = (Haskelly a, Haskelly b)
    Haskelly (a ':\/ b) = Either (Haskelly a) (Haskelly b)
    Haskelly ('S a)     = [Haskelly a]
#ifdef KLEENE_TOP
    Haskelly 'T         = Int
#endif

-- | Convert to haskelly types1
--
-- /Note:/ Inverse would require 'RE' singleton, @SRE@.
haskelly :: Match re xs -> HList xs -> Haskelly re
haskelly MatchE          Nil         = ()
haskelly MatchV          (x ::: Nil) = x
haskelly (MatchA s p q)  xs          = case split s xs of
    ~(x, y) -> (haskelly p x, haskelly q y)
haskelly (MatchL p)      xs          = Left (haskelly p xs)
haskelly (MatchR p)      xs          = Right (haskelly p xs)
haskelly MatchN          Nil         = []
haskelly (MatchC s p q)  xs          = case split s xs of
    ~(x, y) -> haskelly p x : haskelly q y
#ifdef KLEENE_TOP
haskelly (MatchT _)      xs          = hlength xs
#endif

-------------------------------------------------------------------------------
-- Key
-------------------------------------------------------------------------------

-- | /Keyword/, a 'Proxy' kind-specialised to 'Symbol'
--
-- >>> Key @"-l"
-- Key @"foo"
--
data Key (s :: Symbol) = Key deriving Eq

-- | >>> key #foo
-- Key @"foo"
--
key :: Key s -> Key s
key = id

keyVal :: KnownSymbol s => Key s -> String
keyVal = symbolVal

instance s ~ s' => IsLabel s (Key s') where
    fromLabel = Key

instance KnownSymbol s => Show (Key s) where
    showsPrec d k = showParen (d > 10)
        $ showString "K @"
        . showsPrec 11 (keyVal k)

-------------------------------------------------------------------------------
-- Lens
-------------------------------------------------------------------------------

#ifdef MIN_VERSION_lens
-- | Look into 'V'alue.
rval :: Iso (REList (V a)) (REList (V b)) a b
rval = iso f g where
    f :: REList (V a) -> a
    f (REList MatchV (x ::: Nil)) = x
    g x = REList matchV (hsingleton x)

rpair :: Iso (REList (a <> b)) (REList (c <> d)) (REList a, REList b) (REList c, REList d)
rpair = iso f g where
    f :: REList (a <> b) -> (REList a, REList b)
    f (REList (MatchA s p q) zs) = case split s zs of
        ~(xs, ys) -> (REList p xs, REList q ys)

    g (REList p xs, REList q ys) =
        REList (MatchA (hlistToSList xs) p q) (append xs ys)

rfst :: Lens (REList (a <> c)) (REList (b <> c)) (REList a) (REList b)
rfst = rpair . _1

rsnd :: Lens (REList (c <> a)) (REList (c <> b)) (REList a) (REList b)
rsnd = rpair . _2

rsum :: Iso (REList (a \/ b)) (REList (c \/ d)) (Either (REList a) (REList b)) (Either (REList c) (REList d))
rsum = iso f g where
    f :: REList (a \/ b) -> Either (REList a) (REList b)
    f (REList (MatchR p) xs) = Right (REList p xs)
    f (REList (MatchL p) xs) = Left (REList p xs)

    g :: Either (REList a) (REList b) -> REList (a \/ b)
    g (Right (REList p xs)) = REList (MatchR p) xs
    g (Left (REList p xs))  = REList (MatchL p) xs

rleft :: Prism (REList (a \/ c)) (REList (b \/ c)) (REList a) (REList b)
rleft = rsum . _Left

rright :: Prism (REList (c \/ a)) (REList (c \/ b)) (REList a) (REList b)
rright = rsum . _Right

rstar :: Traversal (REList (S a)) (REList (S b)) (REList a) (REList b)
rstar _ (REList MatchN Nil) = pure (REList MatchN Nil)
rstar f (REList (MatchC s p q) zs) = case split s zs of
    ~(xs, ys) -> cons <$> f (REList p xs) <*> rstar f (REList q ys)
  where
    cons :: REList b -> REList (S b) -> REList (S b)
    cons (REList pp xs) (REList qq ys) = REList
        (MatchC (hlistToSList xs) pp qq)
        (append xs ys)

-- TODO: ?
-- type instance Index   (REList (S a)) = Int
-- type instance IxValue (REList (S a)) = REList a
--
-- instance i ~ S a => Ixed (REList i) where ix = ...
--

rnil :: Prism' (REList (S a)) ()
rnil = prism' f g where
    f :: () -> REList (S a)
    f _ = REList MatchN Nil

    g :: REList (S a) -> Maybe ()
    g (REList MatchN Nil)  = Just ()
    g (REList MatchC {} _) = Nothing

rcons :: Prism (REList (S a)) (REList (S b)) (REList a, REList (S a)) (REList b, REList (S b))
rcons = prism f g where
    f :: (REList b, REList (S b)) -> REList (S b)
    f (REList p xs, REList q ys) =
        REList (MatchC (hlistToSList xs) p q) (append xs ys)

    g :: REList (S a) -> Either (REList (S b)) (REList a, REList (S a))
    g (REList MatchN Nil) = Left (REList MatchN Nil)
    g (REList (MatchC s p q) zs) = case split s zs of
        ~(xs, ys) -> Right (REList p xs, REList q ys)

instance AsEmpty (REList (S a)) where _Empty = rnil
instance Cons (REList (S a)) (REList (S b)) (REList a) (REList b) where _Cons = rcons
#endif
