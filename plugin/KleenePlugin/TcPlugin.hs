{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- | Type-checker plugin.
--
-- Solve 'MatchI' constraints.
module KleenePlugin.TcPlugin (tcPlugin) where

import Control.Monad         (guard, (>=>))
import Data.Bifunctor        (first)
import Data.Either           (partitionEithers)
import Data.Foldable         (toList, traverse_)
import Data.Functor.Const    (Const (..))
import Data.Functor.Identity (Identity (..))
import Data.Maybe            (mapMaybe)
import Data.Monoid           (Endo (..))
import Data.Traversable      (for)

import qualified Class      as GHC
import qualified ErrUtils   as Err
import qualified GhcPlugins as GHC
import qualified Outputable as PP
import qualified PrelNames
import qualified TcEvidence as TC
import qualified TcPluginM  as TC
import qualified TcRnTypes  as TC

import qualified Data.Map.Strict as Map

import KleenePlugin.Elaborate
import KleenePlugin.Matching
import KleenePlugin.Names
import KleenePlugin.SWT
import KleenePlugin.Synthesis
import KleenePlugin.TypeEq
import KleenePlugin.Types

-------------------------------------------------------------------------------
-- Type-Checker plugin
-------------------------------------------------------------------------------

tcPlugin :: TC.TcPlugin
tcPlugin = TC.TcPlugin
    { TC.tcPluginInit  = lookupKleNames
    , TC.tcPluginSolve = solveMatchI
    , TC.tcPluginStop  = const (return ())
    }

lookupKleNames :: TC.TcPluginM KleNames
lookupKleNames = do
    GHC.Found _ md <- TC.findImportedModule kleModule Nothing
    cls   <- TC.tcLookupClass =<< TC.lookupOrig md (GHC.mkTcOcc "MatchI")

    -- RE
    reCon  <- TC.tcLookupTyCon =<< TC.lookupOrig md (GHC.mkTcOcc "RE")
    eCon   <- TC.tcLookupDataCon =<< TC.lookupOrig md (GHC.mkDataOcc "E")
    vCon   <- TC.tcLookupDataCon =<< TC.lookupOrig md (GHC.mkDataOcc "V")
    appCon <- TC.tcLookupDataCon =<< TC.lookupOrig md (GHC.mkDataOcc ":<>")
    altCon <- TC.tcLookupDataCon =<< TC.lookupOrig md (GHC.mkDataOcc ":\\/")
    sCon   <- TC.tcLookupDataCon =<< TC.lookupOrig md (GHC.mkDataOcc "S")

    -- Match
    matchECon <- TC.tcLookupDataCon =<< TC.lookupOrig md (GHC.mkDataOcc "MatchE")
    matchVCon <- TC.tcLookupDataCon =<< TC.lookupOrig md (GHC.mkDataOcc "MatchV")
    matchACon <- TC.tcLookupDataCon =<< TC.lookupOrig md (GHC.mkDataOcc "MatchA")
    matchLCon <- TC.tcLookupDataCon =<< TC.lookupOrig md (GHC.mkDataOcc "MatchL")
    matchRCon <- TC.tcLookupDataCon =<< TC.lookupOrig md (GHC.mkDataOcc "MatchR")
    matchNCon <- TC.tcLookupDataCon =<< TC.lookupOrig md (GHC.mkDataOcc "MatchN")
    matchCCon <- TC.tcLookupDataCon =<< TC.lookupOrig md (GHC.mkDataOcc "MatchC")

    -- SList
    snil  <- TC.tcLookupDataCon =<< TC.lookupOrig md (GHC.mkDataOcc "SNil")
    scons <- TC.tcLookupDataCon =<< TC.lookupOrig md (GHC.mkDataOcc "SCons")

    -- Append
    app <- TC.tcLookupTyCon =<< TC.lookupOrig md (GHC.mkTcOcc "Append")

    -- IsLabel
    label <- TC.tcLookupClass PrelNames.isLabelClassName

    -- Key
    key  <- TC.tcLookupTyCon =<< TC.lookupOrig md (GHC.mkTcOcc "Key")

#ifdef KLEENE_TOP
    tCon   <- TC.tcLookupDataCon =<< TC.lookupOrig md (GHC.mkDataOcc "T")
    matchTCon <- TC.tcLookupDataCon =<< TC.lookupOrig md (GHC.mkDataOcc "MatchT")
#endif

    return KleNames
        { kleCls   = cls
        , kleRe    = reCon
        , kleE     = eCon
        , kleV     = vCon
        , kleApp   = appCon
        , kleAlt   = altCon
        , kleS     = sCon
        , kleME    = matchECon
        , kleMV    = matchVCon
        , kleMA    = matchACon
        , kleML    = matchLCon
        , kleMR    = matchRCon
        , kleMN    = matchNCon
        , kleMC    = matchCCon
        , kleSNil  = snil
        , kleSCons = scons
        , kleFApp  = app
        , kleLabel = label
        , kleKey   = key
#ifdef KLEENE_TOP
        , kleT     = tCon
        , kleMT    = matchTCon
#endif
        }
  where
    kleModule  = GHC.mkModuleName "Kleene.Type"

solveMatchI
    :: KleNames  -- ^ MatchI's names
    -> [TC.Ct]   -- ^ [G]iven constraints
    -> [TC.Ct]   -- ^ [D]erived constraints
    -> [TC.Ct]   -- ^ [W]anted constraints
    -> TC.TcPluginM TC.TcPluginResult
solveMatchI kle@KleNames {..} _ _ wanteds = do
    results <- for wantedsMatchI $ \(ct, re, str) ->
        (,) ct <$> solve kle labels ct re str
    case partition results of
        ([], []) ->
            return $ TC.TcPluginOk [] []
        ((e, ct) : errs, []) -> do
            TC.tcPluginIO e
            traverse_ (TC.tcPluginIO . fst) errs
            return $ TC.TcPluginContradiction [ct]
        (errs, ok@(_ : _)) ->
            return $ TC.TcPluginOk (map (first fst) ok) (concatMap (snd . fst) ok ++ map snd errs)
  where
    wantedsMatchI = mapMaybe (findClassConstraint2 kleCls) wanteds

    labels :: Map.Map GHC.TyVar GHC.FastString
    labels = Map.fromList $ mapMaybe (findClassConstraint2 kleLabel >=> elaborateLbl) wanteds

    elaborateLbl (_, sym, var) = do
        var' <- GHC.getTyVar_maybe var
        sym' <- GHC.isStrLitTy sym
        return (var', sym')

    partition :: [(a,Either b c)] -> ([(b,a)], [(c,a)])
    partition []                  = ([], [])
    partition ((k, Right v) : xs) = ([], [(v,k)]) <> partition xs
    partition ((k, Left e) : xs)  = ([(e,k)], []) <> partition xs

solve
    :: KleNames
    -> Map.Map GHC.TyVar GHC.FastString  -- ^ IsLabel map
    -> TC.Ct                             -- ^ Constraint (we extract location :)
    -> GHC.Type                          -- ^ regular expression
    -> GHC.Type                          -- ^ list
    -> TC.TcPluginM (Either (IO ()) (TC.EvTerm, [TC.Ct]))
solve kle labels ct re str = do
    let ctloc = TC.ctLoc ct
    let l = GHC.RealSrcSpan $ TC.ctLocSpan ctloc

    dflags <- TC.unsafeTcPluginTcM GHC.getDynFlags
    famInstEnvs <- TC.getFamInstEnvs

    -- TC.tcPluginIO $ putStrLn "=== MatchI synthesis ==========================="
    -- -- TC.tcPluginIO $ putStrLn $ "MatchI str: " ++ SYB.gshow (elaborateStr kle str)
    -- TC.tcPluginIO $ putStrLn $ "Type re:  " ++ GHC.showPpr dflags re
    -- TC.tcPluginIO $ putStrLn $ "Type str: " ++ GHC.showPpr dflags str

    -- TODO: use exceptT ?
    case (elaborateStr kle str, elaborateRe kle re) of
        (Left err, _) -> return $ Left $
            GHC.putLogMsg dflags GHC.NoReason Err.SevError l  (GHC.defaultErrStyle dflags) $ bullets
                [ PP.hang (PP.text "Cannot elaborate type level list") 2 $
                    PP.ppr str
                , PP.text err
                ]
        (_, Left err) -> return $ Left $
            GHC.putLogMsg dflags GHC.NoReason Err.SevError l  (GHC.defaultErrStyle dflags) $ bullets
                [ PP.hang (PP.text "Cannot elaborate type level RE") 2 $
                    PP.ppr re
                , PP.text err
                ]
        (Right str', Right re') ->
            -- TC.tcPluginIO $ putStrLn $ "Elab re:  " ++ show (GHC.showPpr dflags <$> re')
            -- TC.tcPluginIO $ putStrLn $ "Elab str: " ++ GHC.showPpr dflags str'

            case matches (maybeEqType kle labels) re' str' of
                Right proofs -> case partitionProofs proofs of
                    ([pf], _) -> do
                        -- TC.tcPluginIO $ putStrLn $ "Res re:  " ++ GHC.showPpr dflags re'
                        -- TC.tcPluginIO $ putStrLn $ "Res cs:  " ++ GHC.showPpr dflags str'
                        -- TC.tcPluginIO $ putStrLn $ "Res pf:  " ++ GHC.showPpr dflags pf

                        let Identity pf' = traverseProofC (\a _ () -> return $ GHC.mkNomReflCo a) pf
                        let e = synProof famInstEnvs kle pf'
                        return $ Right (makeEvidence2 (kleCls kle) e re str, [])

                    -- No rigid proofs, need to solve constraints
                    ([], proofs') -> case filterProofs proofs' of
                        (errs, []) -> return $ Left $
                            GHC.putLogMsg dflags GHC.NoReason Err.SevError l (GHC.defaultErrStyle dflags) $ bullets
                                [ PP.text "Regular expression doesn't match"
                                , PP.hang (PP.text "Regular expression") 2 $
                                    PP.ppr re'
                                , PP.hang (PP.text "Type list") 2 $
                                    PP.ppr str'
                                , PP.text "There is no way for type-variables to unify in:"
                                    PP.$$
                                    PP.nest 2 (bullets
                                        [ PP.sep [ PP.ppr pf PP.<> PP.char ':',  PP.ppr err ]
                                        | (err, pf) <- toList errs
                                        ])
                                ]

                        (_, [pf]) -> do
                            let mkCo a _ Nothing               = return $ GHC.mkNomReflCo a
                                mkCo a b (Just (MayUnify _ _)) = do
                                    hole <- liftSWT $ TC.newCoercionHole GHC.liftedTypeKind
                                    tellSingleSWT (hole, a, b)
                                    return (GHC.mkHoleCo hole)
                                    -- return $ GHC.mkUnivCo (TyCoRep.PluginProv "kleene-types") TC.Nominal a b

                            (holes, pf') <- runSWT $ traverseProofC mkCo pf
                            let e = synProof famInstEnvs kle pf'

                            return $ Right (makeEvidence2 (kleCls kle) e re str, map (unifyItemToCt ctloc) holes)

                        (_errs, pfs) -> return $ Left $
                            GHC.putLogMsg dflags GHC.NoReason Err.SevError l (GHC.defaultErrStyle dflags) $ bullets
                                [ PP.text "Ambiguous matches"
                                , PP.hang (PP.text "Regular expression") 2 $
                                    PP.ppr re'
                                , PP.hang (PP.text "Type list") 2 $
                                    PP.ppr str'
                                -- TODO: print equalities
                                , PP.text "Possible matches are:"
                                    PP.$$
                                    PP.nest 2 (PP.vcat [ PP.bullet PP.<+> PP.ppr pf | pf <- toList pfs ])
                                ]

                    (pfs, _) -> return $ Left $
                        GHC.putLogMsg dflags GHC.NoReason Err.SevError l (GHC.defaultErrStyle dflags) $ bullets
                            [ PP.text "Regular expression doesn't match"
                            , PP.hang (PP.text "Regular expression") 2 $
                                PP.ppr re'
                            , PP.hang (PP.text "Type list") 2 $
                                PP.ppr str'
                            , PP.text "Possible matches are:"
                                PP.$$
                                PP.nest 2 (PP.vcat [ PP.bullet PP.<+> PP.ppr pf | pf <- toList pfs ])
                            ]

                Left (UnexpectedEnd r as) -> return $ Left $
                    GHC.putLogMsg dflags GHC.NoReason Err.SevError l (GHC.defaultErrStyle dflags) $ bullets
                        [ PP.text "Regular expression doesn't match: unexpected end-of-input"
                        , PP.hang (PP.text "Regular expression") 2 $
                            PP.ppr re'
                        , PP.hang (PP.text "Type list") 2 $
                            PP.ppr str'
                        , PP.hang (PP.text "In a matching state") 2 $
                            PP.ppr (simplifyRE r)
                        , PP.hsep
                            [ PP.text "Expecting"
                            , PP.pprWithCommas PP.ppr as
                            ]
                        ]

                Left (NonMatch r c cs as) -> return $ Left $
                    GHC.putLogMsg dflags GHC.NoReason Err.SevError l (GHC.defaultErrStyle dflags) $ bullets
                        [ PP.text "Regular expression doesn't match, unexpected" PP.<+> PP.ppr c
                        , PP.hang (PP.text "Regular expression") 2 $
                            PP.ppr re'
                        , PP.hang (PP.text "Type list") 2 $
                            PP.ppr str'
                        , PP.hang (PP.text "In a matching state") 2 $
                            PP.ppr (simplifyRE r)
                        , PP.hsep
                            [ PP.text "Unexpected"
                            , PP.quotes (PP.ppr c)
                            , PP.text "followed by"
                            , PP.ppr cs
                            ]
                        , PP.hsep
                            [ PP.text "Expecting"
                            , PP.pprWithCommas (maybe (PP.text "end-of-list") PP.ppr) as
                            ]
                        ]

bullets :: [PP.SDoc] -> PP.SDoc
bullets = PP.vcat . map (PP.bullet PP.<+>)

type Proof' = Proof (Maybe UnifResult) GHC.Type GHC.Type

filterProofs :: Foldable f => f Proof' -> ([(UF, Proof')], [Proof'])
filterProofs = partitionEithers . map proofConstraints . toList where
    proofConstraints :: Proof' -> Either (UF, Proof') Proof'
    proofConstraints pf = case manyMayUnify constraints of
        Left err -> Left (err, pf)
        Right () -> Right pf
      where
        constraints :: [UnifResult]
        constraints = appEndo (getConst (traverseProofC f pf)) []

        f _ _ Nothing   = Const (Endo id)
        f _ _ (Just ur) = Const (Endo (ur :))


-- | Split proofs into with additional constraints and one without.
partitionProofs
    :: Foldable f
    => f (Proof (Maybe UnifResult) GHC.Type GHC.Type)
    -> ([Proof () GHC.Type GHC.Type], [Proof (Maybe UnifResult) GHC.Type GHC.Type])
partitionProofs pfs = partitionEithers $ map f $ toList pfs where
    f pf = case traverseProofC g pf of
        Just pf' -> Left pf'
        Nothing  -> Right pf

    g _ _ Nothing  = Just ()
    g _ _ (Just _) = Nothing

-------------------------------------------------------------------------------
-- Helpers
-------------------------------------------------------------------------------

findClassConstraint2 :: GHC.Class -> TC.Ct -> Maybe (TC.Ct, GHC.Type, GHC.Type)
findClassConstraint2 cls ct = do
    (cls', [re, str]) <- GHC.getClassPredTys_maybe (TC.ctPred ct)
    guard (cls' == cls)
    return (ct, re, str)

makeEvidence2 :: GHC.Class -> GHC.CoreExpr -> GHC.Type -> GHC.Type -> TC.EvTerm
makeEvidence2 cls e ty ty2 = TC.EvExpr appDc
  where
    tyCon = GHC.classTyCon cls
    dc    = GHC.tyConSingleDataCon tyCon
    appDc = GHC.mkCoreConApps dc [GHC.Type ty, GHC.Type ty2, e]

unifyItemToCt :: TC.CtLoc -> (TC.CoercionHole, GHC.Type, GHC.Type) -> TC.Ct
unifyItemToCt loc (hole, a, b) = TC.mkNonCanonical $
    TC.CtWanted (GHC.mkPrimEqPred a b) (TC.HoleDest hole) TC.WDeriv loc
