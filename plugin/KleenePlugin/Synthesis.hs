-- | Core synthesis.
--
-- We transform from our types to 'GHC.CoreExpr' or 'GHC.Type'.
-- The code is very direct, but we have to provide everything
-- (type and coercion arguments!) manually.
module KleenePlugin.Synthesis where

import KleenePlugin.Names
import KleenePlugin.Types

import           FamInst    (FamInstEnvs)
import qualified FamInstEnv
import qualified GhcPlugins as GHC

-------------------------------------------------------------------------------
-- Synthesis: List
-------------------------------------------------------------------------------

-- | synthesise type level list (of types).
synStrType :: [GHC.Type] -> GHC.Type
synStrType = foldr f z where
    z = GHC.mkTyConApp (GHC.promoteDataCon GHC.nilDataCon)
        [ GHC.liftedTypeKind
        ]

    f x xs = GHC.mkTyConApp (GHC.promoteDataCon GHC.consDataCon)
        [ GHC.liftedTypeKind
        , x
        , xs
        ]

-------------------------------------------------------------------------------
-- Synthesis: SList
-------------------------------------------------------------------------------

-- | synthesise 'SList' value.
synSList :: KleNames -> [GHC.Type] -> GHC.CoreExpr
synSList kle = go where
    go []       = GHC.mkCoreConApps (kleSNil kle)
        [ GHC.Type $ synStrType []
        , GHC.Coercion $ GHC.mkNomReflCo $ synStrType []
        ]
    go (x : xs) = GHC.mkCoreConApps (kleSCons kle)
        [ GHC.Type xxsTy
        , GHC.Type x
        , GHC.Type $ synStrType xs
        , GHC.Coercion $ GHC.mkNomReflCo xxsTy
        , go xs
        ]
      where
        xxsTy = synStrType $ x : xs

-------------------------------------------------------------------------------
-- Synthesis: Proof
-------------------------------------------------------------------------------

-- | synthesise 'Match' from 'Proof'.
synProof
    :: FamInstEnvs
    -> KleNames
    -> Proof GHC.Coercion GHC.Type GHC.Type -> GHC.CoreExpr -- TODO: c -> Coercion
synProof fam kle = go where
    nilTy     = synStrType []
    nilReflCo = GHC.mkNomReflCo nilTy

    go ProofE = GHC.mkCoreConApps (kleME kle)
        [ GHC.Type reTy
        , GHC.Type nilTy
        , GHC.Coercion $ GHC.mkNomReflCo reTy
        , GHC.Coercion   nilReflCo
        ]
      where
        reTy = synReType kle E

    go (ProofV co a t) = GHC.mkCoreConApps (kleMV kle)
        [ GHC.Type reTy
        , GHC.Type ts
        , GHC.Type a
        , GHC.Coercion $ GHC.mkNomReflCo reTy
        , GHC.Coercion $ GHC.mkTyConAppCo GHC.Nominal (GHC.promoteDataCon GHC.consDataCon)
            [ GHC.mkNomReflCo GHC.liftedTypeKind
            , co
            , GHC.mkTyConAppCo GHC.Nominal (GHC.promoteDataCon GHC.nilDataCon)
                [ GHC.mkNomReflCo GHC.liftedTypeKind
                ]
            ]
        ]
      where
        reTy = synReType kle (V t)
        ts   = synStrType [a]

    go (ProofA r s xs ys p q) = GHC.mkCoreConApps (kleMA kle)
        -- tracePpr "debug" ((xs, xsTy), (ys, ysTy), (zs, zsTy), (xsAppYs, _zs)) $
        [ GHC.Type reTy
        , GHC.Type zsTy
        , GHC.Type rTy
        , GHC.Type sTy
        , GHC.Type xsTy
        , GHC.Type ysTy
        , GHC.Coercion $ GHC.mkNomReflCo reTy
        , GHC.Coercion   co
        , synSList kle xs
        , go p
        , go q
        ]
      where
        reTy = synReType kle (r :<> s)
        rTy  = synReType kle r
        sTy  = synReType kle s

        zs = xs ++ ys

        xsTy = synStrType xs
        ysTy = synStrType ys
        zsTy = synStrType zs

        xsAppYs = GHC.mkTyConApp (kleFApp kle) [ xsTy, ysTy ]

        -- TODO?: internal check: _zs = zs
        (co0, _zs) = FamInstEnv.normaliseType fam GHC.Nominal xsAppYs
        co = GHC.mkSymCo co0

    go (ProofL r s xs p) = GHC.mkCoreConApps (kleML kle)
          [ GHC.Type reTy
          , GHC.Type (synStrType xs)
          , GHC.Type rTy
          , GHC.Type sTy
          , GHC.Coercion $ GHC.mkNomReflCo reTy
          , go p
          ]
      where
        reTy = synReType kle (r :\/ s)
        rTy  = synReType kle r
        sTy  = synReType kle s

    go (ProofR r s xs p) = GHC.mkCoreConApps (kleMR kle)
        [ GHC.Type reTy
        , GHC.Type (synStrType xs)
        , GHC.Type rTy
        , GHC.Type sTy
        , GHC.Coercion $ GHC.mkNomReflCo reTy
        , go p
        ]
      where
        reTy = synReType kle (r :\/ s)
        rTy  = synReType kle r
        sTy  = synReType kle s

    go (ProofN re) = GHC.mkCoreConApps (kleMN kle)
        [ GHC.Type re0Ty
        , GHC.Type nilTy
        , GHC.Type reTy
        , GHC.Coercion $ GHC.mkNomReflCo re0Ty
        , GHC.Coercion   nilReflCo
        ]
      where
        re0Ty = synReType kle (S re)
        reTy  = synReType kle re

    go (ProofC re xs ys p q) = GHC.mkCoreConApps (kleMC kle)
        [ GHC.Type re0Ty
        , GHC.Type zsTy
        , GHC.Type reTy
        , GHC.Type xsTy
        , GHC.Type ysTy
        , GHC.Coercion $ GHC.mkNomReflCo re0Ty
        , GHC.Coercion   co
        , synSList kle xs
        , go p
        , go q
        ]
      where
        re0Ty = synReType kle (S re)
        reTy  = synReType kle re

        zs = xs ++ ys

        xsTy = synStrType xs
        ysTy = synStrType ys
        zsTy = synStrType zs

        xsAppYs = GHC.mkTyConApp (kleFApp kle) [ xsTy, ysTy ]

        -- TODO?: internal check: _zs = zs
        (co0, _zs) = FamInstEnv.normaliseType fam GHC.Nominal xsAppYs
        co = GHC.mkSymCo co0
#ifdef KLEENE_TOP
    go (ProofT xs) = GHC.mkCoreConApps (kleMT kle)
        [ GHC.Type re0Ty
        , GHC.Type xsTy
        , GHC.Coercion $ GHC.mkNomReflCo re0Ty
        , synSList kle xs
        ]
      where
        re0Ty = synReType kle T
        xsTy = synStrType xs
#endif

-------------------------------------------------------------------------------
-- Synthesis: RE
-------------------------------------------------------------------------------

-- | Synthesise type level 'RE' (of types).
synReType :: KleNames -> RE GHC.Type -> GHC.Type
synReType kle = go where
    go E = GHC.mkTyConApp (GHC.promoteDataCon $ kleE kle)
        [ GHC.liftedTypeKind
        ]
    go (V ty) = GHC.mkTyConApp (GHC.promoteDataCon $ kleV kle)
        [ GHC.liftedTypeKind
        , ty
        ]
    go (S re) = GHC.mkTyConApp (GHC.promoteDataCon $ kleS kle)
        [ GHC.liftedTypeKind
        , go re
        ]
    go (a :<> b) = GHC.mkTyConApp (GHC.promoteDataCon $ kleApp kle)
        [ GHC.liftedTypeKind
        , go a
        , go b
        ]
    go (a :\/ b) = GHC.mkTyConApp (GHC.promoteDataCon $ kleAlt kle)
        [ GHC.liftedTypeKind
        , go a
        , go b
        ]
#ifdef KLEENE_TOP
    go T = GHC.mkTyConApp (GHC.promoteDataCon $ kleT kle)
        [ GHC.liftedTypeKind
        ]
#endif
