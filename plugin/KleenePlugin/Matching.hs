{-# LANGUAGE ScopedTypeVariables #-}
-- | Match 'RE' on a list (and produce a 'Proof').
module KleenePlugin.Matching where

import Control.Applicative ((<|>))
import Data.List.NonEmpty  (NonEmpty (..))
import Data.Maybe          (isJust, maybeToList)

import qualified Outputable         as PP

import KleenePlugin.Types

-------------------------------------------------------------------------------
-- Leading characters
-------------------------------------------------------------------------------

leading :: RE a -> [a]
leading E = []
leading (V a) = [a]
leading (a :\/ b) = leading a <> leading b
leading (a :<> b)
    | isJust (nullable a) = leading a <> leading b
    | otherwise           = leading a
leading (S a) = leading a
#ifdef KLEENE_TOP
leading T = [] -- well, technically "anything"
#endif

-------------------------------------------------------------------------------
-- Matches
-------------------------------------------------------------------------------

data MatchingError b a
    = UnexpectedEnd (RE a) [a]
    | NonMatch (RE a) b [b] [Maybe a]

-- | Return a list of match-proofs of @re@ to @cs@.
--
-- @
-- matches : (re : Re) → (cs : List *) → List (Proof re cs)
-- @
--
matches
    :: (PP.Outputable a, PP.Outputable b)
    => (a -> b -> Either c Bool)  -- ^ @a,b@-equality
    -> RE a                       -- ^ regular expression
    -> [b]                        -- ^ string
    -> Either (MatchingError b a) (NonEmpty (Proof (Maybe c) b a))
matches _eq re []       = case nullable re of
    Just pf -> Right (pure pf)
    Nothing -> Left $ UnexpectedEnd re $ {- nubBy eq $ -} leading re
matches eq re (c : cs) = case derivate eq c re of
    [] -> Left $ NonMatch re c cs $
        maybe [] (const [Nothing]) (nullable re) ++
        fmap Just (leading re) -- (nubBy eq (leading re))
    (d:ds) ->
        (d :| ds)         >>>= \(re', endo) ->
        matches eq re' cs <&&> \p ->
        endo p

infixl 1 >>>=, <&&>

-- | Note: not @fmap join $ traverse f xs@
(>>>=) :: NonEmpty a -> (a -> Either e (NonEmpty b)) -> Either e (NonEmpty b)
xs >>>= f = acc $ fmap f xs where
    acc :: NonEmpty (Either e (NonEmpty b)) -> Either e (NonEmpty b)
    acc (x :| []) = x
    acc (x :| y : zs) = comb x (acc (y :| zs))

    comb :: Either e (NonEmpty b) -> Either e (NonEmpty b) -> Either e (NonEmpty b)
    comb (Left e) (Left _)   = Left e
    comb (Left _) (Right y)  = Right y
    comb (Right x) (Left _)  = Right x
    comb (Right x) (Right y) = Right (x <> y)

(<&&>) :: (Functor f, Functor g) => f (g a) -> (a -> b) -> f (g b)
x <&&> f = fmap (fmap f) x

-- |
--
-- @
-- nullable : (re : Re) → Maybe (Proof re [])
-- @
--
nullable :: RE a -> Maybe (Proof (Maybe c) b a)
nullable E         = return ProofE
nullable (V _)     = Nothing
nullable (a :<> b) = ProofA a b [] []
    <$> nullable a
    <*> nullable b
nullable (a :\/ b) =
    ProofL a b [] <$> nullable a <|>
    ProofR a b [] <$> nullable b
nullable (S re)    = return (ProofN re)
#ifdef KLEENE_TOP
nullable T         = return (ProofT [])
#endif

-- |
--
-- @
-- derivate
--   : (c : *) → (re : Re)
--   → List (Σ Re λ re′ → (cs : List *) → Proof re′ cs → Proof re (c ∷ cs))
-- @
derivate
    :: forall a b c. (PP.Outputable a, PP.Outputable b)
    => (a -> b -> Either c  Bool)                             -- ^ atom decidable equality
    -> b                                                      -- ^ atom
    -> RE a                                                   -- ^ regular expression
    -> [(RE a, Proof (Maybe c) b a -> Proof (Maybe c) b a)]   -- ^ result
derivate _ _ E = []
derivate eq c (V b) = case eq b c of
    Right False -> []
    Right True  -> return $ exists E $ \p -> case p of
        ProofE -> ProofV Nothing c b
        _      -> error $ "panic! Proof for E isn't ProofE, but "
            ++ PP.showSDocUnsafe (PP.ppr p)
            ++ "\n  : " ++ PP.showSDocUnsafe (PP.ppr (proofTy p))
            ++ "\n  : " ++ PP.showSDocUnsafe (PP.ppr (proofStr p))
    Left x      -> return $ exists E $ \p -> case p of
        ProofE -> ProofV (Just x) c b
        _      -> error $ "panic! Proof for E isn't ProofE, but "
            ++ PP.showSDocUnsafe (PP.ppr p)
            ++ "\n  : " ++ PP.showSDocUnsafe (PP.ppr (proofTy p))
            ++ "\n  : " ++ PP.showSDocUnsafe (PP.ppr (proofStr p))
derivate eq c (r :<> s) = dr <|> ds where
    dr :: [(RE a, Proof (Maybe c) b a -> Proof (Maybe c) b a)]
    dr = do
        (r', endo) <- derivate eq c r
        return $ exists (r' :<> s) $ \p -> appendLemma c r endo p

    ds :: [(RE a, Proof (Maybe c) b a -> Proof (Maybe c) b a)]
    ds = do
        p          <- maybeToList $ nullable r
        (s', endo) <- derivate eq c s
        return $ exists s' $ \q ->
            ProofA r s [] (c : proofStr q) p (endo q)

derivate eq c (r :\/ s) = dr <|> ds where
    dr :: [(RE a, Proof (Maybe c) b a -> Proof (Maybe c) b a)]
    dr = do
        (r', endo) <- derivate eq c r
        return $ exists r' $ \p ->
            ProofL r s (c : proofStr p) (endo p)

    ds :: [(RE a, Proof (Maybe c) b a  -> Proof (Maybe c) b a)]
    ds = do
        (s', endo) <- derivate eq c s
        return $ exists s' $ \p ->
            ProofR r s (c : proofStr p) (endo p)

derivate eq c (S r) = do
    (r', endo) <- derivate eq c r
    return $ exists (r' :<> S r) $ \p -> starLemma c r endo p
#ifdef KLEENE_TOP
derivate _eq c T = consume where
    consume :: [(RE a, Proof (Maybe c) b a  -> Proof (Maybe c) b a)]
    consume = return $ exists T $ \p -> case p of
        ProofT xs -> ProofT (c : xs)
        _      -> error $ "panic! Proof for T isn't ProofT, but "
            ++ PP.showSDocUnsafe (PP.ppr p)
            ++ "\n  : " ++ PP.showSDocUnsafe (PP.ppr (proofTy p))
            ++ "\n  : " ++ PP.showSDocUnsafe (PP.ppr (proofStr p))
#endif

exists
    :: RE a -> (Proof (Maybe c) b a -> Proof (Maybe c) b a)
    -> (RE a, Proof (Maybe c) b a -> Proof (Maybe c) b a)
exists = (,)

-- | Append Lemma for implementation of 'derivate'.
--
-- @
-- append-lemma {c} {r} {cs} f r′s =
--   let pair r′ s = r′s
--   in pair (f r′) s
-- @
--
-- /Note:/ As we don't have left rules in 'Proof',
-- @r′s@ __must__ be 'ProofA'.
appendLemma
    :: (PP.Outputable a, PP.Outputable b)
    => b                                             -- ^ @(c : *)@
    -> RE a                                          -- ^ @(r : RE)@
    -> (Proof (Maybe c) b a -> Proof (Maybe c) b a)  -- ^ @((cs′ : List *) → Proof r′ cs′ → Proof r (c ∷ cs′))@
    -> Proof (Maybe c) b a                           -- ^ @Proof (r′ ∙ s) cs@
    -> Proof (Maybe c) b a                           -- ^ @Proof (r ∙ s) (c ∷ cs)@
appendLemma c r f (ProofA _r' s xs ys p q) =
{-
  tracePpr "append-lemma"
  ( (Ta "params", c, cs)
  , (Ta "r'", r', xs, p)
  , (Ta "s", s, ys, q)
  , (Ta "r", r, (c : xs), f cs p)
  , (Ta "x", (r :<> s), (c : xs ++ ys), ProofA r s (c : xs) ys (f cs p) q)
  ) $
-}
    ProofA r s (c : xs) ys (f p) q
appendLemma c r _ p = error $ "panic! appendLemma called with not ProofA\n  "
    ++ PP.showSDocUnsafe (PP.ppr p)
    ++ "\n  : " ++ PP.showSDocUnsafe (PP.ppr (proofTy p))
    ++ "\n  : " ++ PP.showSDocUnsafe (PP.ppr (proofStr p))
    ++ "\n  arguments:"
    ++ "\n  c:  " ++ PP.showSDocUnsafe (PP.ppr c)
    ++ "\n  r:  " ++ PP.showSDocUnsafe (PP.ppr r)

-- | Like 'appendLemma' but for kleene star.
starLemma
    :: (PP.Outputable a, PP.Outputable b)
    => b                                             -- ^ @(c : *)@
    -> RE a                                          -- ^ @(r : RE)@
    -> (Proof (Maybe c) b a -> Proof (Maybe c) b a)  -- ^ @((cs′ : List *) → Proof r′ cs′ → Proof r (c ∷ cs′))@
    -> Proof (Maybe c) b a                           -- ^ @Proof (r′ ∙ S r) cs@
    -> Proof (Maybe c) b a                           -- ^ @Proof (S r) (c ∷ cs)@
starLemma c r f (ProofA _r' _s' xs ys p q) =
    ProofC r (c : xs) ys (f p) q

starLemma c r _ p = error $ "panic! appendLemma called with not ProofA\n  "
    ++ PP.showSDocUnsafe (PP.ppr p)
    ++ "\n  : " ++ PP.showSDocUnsafe (PP.ppr (proofTy p))
    ++ "\n  : " ++ PP.showSDocUnsafe (PP.ppr (proofStr p))
    ++ "\n  arguments:"
    ++ "\n  c:  " ++ PP.showSDocUnsafe (PP.ppr c)
    ++ "\n  r:  " ++ PP.showSDocUnsafe (PP.ppr r)

{-
-------------------------------------------------------------------------------
-- Trace
-------------------------------------------------------------------------------

-- | Like GHC.mkCoreConApps but uses dataConWrapId
-- mkConApp :: GHC.DataCon -> [GHC.CoreExpr] -> GHC.CoreExpr
-- mkConApp = GHC.mkCoreApps . GHC.Var . GHC.dataConWrapId

newtype Ta = Ta String

instance PP.Outputable Ta where
    ppr (Ta s) = PP.text s PP.<> PP.char ':'
-}
