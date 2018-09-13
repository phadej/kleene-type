{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor      #-}
module KleenePlugin.Types
    ( RE (..)
    , simplifyRE
    , Proof (..)
    , proofStr
    , proofTy
    , traverseProofC,
    ) where

import qualified Data.Generics as SYB
import qualified Outputable    as PP
import qualified DynFlags

-------------------------------------------------------------------------------
-- RE
-------------------------------------------------------------------------------

-- | Regular expression.
--
-- This is a /copy/ of @Kleene.Type.RE@ type in "Kleene.Type".
data RE a
    = E              -- ^ empty string
    | V a            -- ^ variable
    | RE a :<> RE a  -- ^ append
    | RE a :\/ RE a  -- ^ alternative
    | S (RE a)       -- ^ star
#ifdef KLEENE_TOP
    | T              -- ^ top
    -- | Z              -- ^ zero
#endif
  deriving (Functor, Show, SYB.Data)

-- | Simplify 'RE' structure.
--
-- This is useful when pretty printing 'RE'.
-- \"Real\" use would need to produce a transformation proof ('Proof' cannot express that).
simplifyRE :: RE a -> RE a
simplifyRE r@E {}    = r
simplifyRE r@V {}    = r
simplifyRE (r :<> s) = case (simplifyRE r, simplifyRE s) of
    (E, x)       -> x
    (x, E)       -> x
    (x :<> y, z) -> x :<> simplifyRE (y :<> z)
    (x, y)       -> x :<> y
simplifyRE (r :\/ s) = case (simplifyRE r, simplifyRE s) of
    (x :\/ y, z) -> x :\/ simplifyRE (y :\/ z)
    (x, y)       -> x :\/ y
simplifyRE (S E)     = E
simplifyRE (S (S r)) = simplifyRE (S r)
simplifyRE (S r)     = S (simplifyRE r)
#ifdef KLEENE_TOP
simplifyRE T         = T
-- simplifyRE Z         = Z
#endif


-------------------------------------------------------------------------------
-- Proof
-------------------------------------------------------------------------------

-- | A 'Proof' that regular expression matches.
data Proof c b a
    = ProofE                                   -- ^ @top      : Proof E []@
    | ProofV c b a                             -- ^ @x        : Proof (V a) [a]@
    | ProofA (RE a) (RE a) [b] [b] (Proof c b a) (Proof c b a)
      -- ^ @pair p q : Proof a xs -> Proof b ys -> Proof (a <> b) (xs ++ ys)@
    | ProofL (RE a) (RE a) [b] (Proof c b a)   -- ^ @inl p    : Proof a xs -> Proof (a \\/ b) xs@
    | ProofR (RE a) (RE a) [b] (Proof c b a)   -- ^ @inr q    : Proof b xs -> Proof (a \\/ b) xs@
    | ProofN (RE a)                            -- ^ @nil      : Proof (S re) []@
    | ProofC (RE a) [b] [b] (Proof c b a) (Proof c b a)
      -- ^ @cons p q : Proof a xs -> Proof (S a) ys -> Proof (S a) (xs ++ ys)@
#ifdef KLEENE_TOP
    | ProofT [b]                               -- ^ @top      : Proof T xs@
#endif
  deriving (Functor, Show, SYB.Data)

traverseProofC :: Applicative f => (a -> b -> c -> f c') -> Proof c b a -> f (Proof c' b a)
traverseProofC f = go where
    go ProofE                 = pure ProofE
    go (ProofV c b a)         = (\c' -> ProofV c' b a)
        <$> f a b c
    go (ProofA r s xs ys p q) = ProofA r s xs ys
        <$> go p
        <*> go q
    go (ProofL r s xs p)      = ProofL r s xs <$> go p
    go (ProofR r s xs p)      = ProofR r s xs <$> go p
    go (ProofN r)             = pure (ProofN r)
    go (ProofC r xs ys p q)   = ProofC r xs ys
        <$> go p
        <*> go q
#ifdef KLEENE_TOP
    go (ProofT xs)            = pure (ProofT xs)
#endif

-- | What string the 'Proof' matches. It's enough to look at the top level.
proofStr :: Proof c b a -> [b]
proofStr ProofE                  = []
proofStr (ProofV _ b _)          = [b]
proofStr (ProofA _ _ xs ys _ _ ) = xs ++ ys
proofStr (ProofL _ _ xs _)       = xs
proofStr (ProofR _ _ xs _)       = xs
proofStr (ProofN _)              = []
proofStr (ProofC _ xs ys _ _)    = xs ++ ys
#ifdef KLEENE_TOP
proofStr (ProofT xs)             = xs
#endif

-- | What regex the 'Proof' executes. It's enough to look at the top level.
proofTy :: Proof c b a -> RE a
proofTy ProofE               = E
proofTy (ProofV _ _ t)       = V t
proofTy (ProofA r s _ _ _ _) = r :<> s
proofTy (ProofL r s _ _)     = r :\/ s
proofTy (ProofR r s _ _)     = r :\/ s
proofTy (ProofN r)           = S r
proofTy (ProofC r _ _ _ _)   = S r
#ifdef KLEENE_TOP
proofTy (ProofT _)           = T
#endif

-------------------------------------------------------------------------------
-- Outputable RE
-------------------------------------------------------------------------------

instance PP.Outputable a => PP.Outputable (RE a) where
    pprPrec _ E           = PP.unicodeSyntax (PP.text "ε") (PP.text "[]")
    pprPrec d (V a)       = PP.pprPrec d a
    pprPrec d a@(_ :<> _) = PP.cparen (d > 6) $ PP.sep $
        punctuate (PP.unicodeSyntax (PP.char '⋅') (PP.text "<>")) $
        map (PP.pprPrec 6) (peelApp a)
    pprPrec d a@(_ :\/ _) = PP.cparen (d > 5) $ PP.sep $
        punctuate (PP.unicodeSyntax (PP.char '∨') (PP.text "\\/")) $
        map (PP.pprPrec 6) (peelAlt a)
    pprPrec d (S r)       = PP.cparen (d > 10) $
        PP.hang (PP.text "list") 2 $
        PP.pprPrec 11 r
#ifdef KLEENE_TOP
    pprPrec _ T           = PP.unicodeSyntax (PP.text "⊤") (PP.text "T")
    -- pprPrec _ Z           = PP.unicodeSyntax (PP.text "∅") (PP.text "Z")
#endif

-- | Like 'PP.punctuate' but using '<+>'
punctuate
    :: PP.SDoc   -- ^ The punctuation
    -> [PP.SDoc] -- ^ The list that will have punctuation added between every adjacent pair of elements
    -> [PP.SDoc] -- ^ Punctuated list
punctuate _ []     = []
punctuate p (x:xs) = go x xs where
    go d []     = [d]
    go d (e:es) = (d PP.<+> p) : go e es

peelApp :: RE a -> [RE a]
peelApp (a :<> b) = a : peelApp b
peelApp a         = [a]

peelAlt :: RE a -> [RE a]
peelAlt (a :\/ b) = a : peelAlt b
peelAlt a         = [a]

-------------------------------------------------------------------------------
-- Outputable Expr
-------------------------------------------------------------------------------

-- | We print type applications when @-fprint-explicit-foralls@ is on.
pprExpr :: DynFlags.DynFlags -> Rational -> String -> [PP.SDoc] -> [PP.SDoc] -> PP.SDoc
pprExpr dflags d f xs ys
    | null zs   = PP.text f
    | otherwise = PP.cparen (d > 10) $ PP.hang (PP.text f) 2 $ PP.sep zs
  where
    zs | DynFlags.gopt DynFlags.Opt_PrintExplicitForalls dflags = xs ++ ys
       | otherwise                                              = ys

pprPrecTerm :: (PP.Outputable a, PP.Outputable b) => DynFlags.DynFlags -> Rational -> Proof c b a -> PP.SDoc
pprPrecTerm dflags = go where
    go _ ProofE         = PP.text "top"
    go d (ProofV _ _ t) = PP.pprPrec d t
    go d (ProofA r s xs ys p q) = pprExpr dflags d "times"
        [ PP.char '@' PP.<> PP.pprPrec 11 r
        , PP.char '@' PP.<> PP.pprPrec 11 s
        , PP.char '#' PP.<> PP.ppr xs
        , PP.char '#' PP.<> PP.ppr ys
        ]
        [ go 11 p
        , go 11 q
        ]
    go d (ProofR r s xs p) = pprExpr dflags d "inr"
        [ PP.char '@' PP.<> PP.pprPrec 11 r
        , PP.char '@' PP.<> PP.pprPrec 11 s
        , PP.char '#' PP.<> PP.ppr xs
        ]
        [ go 11 p
        ]
    go d (ProofL r s xs p) = pprExpr dflags d "inl"
        [ PP.char '@' PP.<> PP.pprPrec 11 r
        , PP.char '@' PP.<> PP.pprPrec 11 s
        , PP.char '#' PP.<> PP.ppr xs
        ]
        [ go 11 p
        ]
    go d (ProofN re) = pprExpr dflags d "nil"
        [ PP.char '@' PP.<> PP.pprPrec 11 re
        ]
        []
    go d (ProofC re xs ys p q) = pprExpr dflags d "cons"
        [ PP.char '@' PP.<> PP.pprPrec 11 re
        , PP.char '#' PP.<> PP.ppr xs
        , PP.char '#' PP.<> PP.ppr ys
        ]
        [ go 11 p
        , go 11 q
        ]
#ifdef KLEENE_TOP
    go d (ProofT xs) = pprExpr dflags d "top"
        [ PP.char '#' PP.<> PP.ppr xs
        ]
        []
#endif

instance (PP.Outputable a, PP.Outputable b) => PP.Outputable (Proof c b a) where
    pprPrec d proof = PP.sdocWithDynFlags $ \flags -> pprPrecTerm flags d proof
