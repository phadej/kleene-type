-- | Elaboration.
--
-- Convert from 'GHC.Type' to our types.
module KleenePlugin.Elaborate where

import KleenePlugin.Names
import KleenePlugin.Types

import qualified GhcPlugins as GHC

-- | Elaborate type-level 'RE' (of types).
elaborateRe :: KleNames -> GHC.Type -> Either String (RE GHC.Type)
elaborateRe kle = go where
    go ty0
        | Just (tyCon, [k]) <- GHC.splitTyConApp_maybe ty0
        , GHC.eqType k GHC.liftedTypeKind
        , Just dataCon <- GHC.isPromotedDataCon_maybe tyCon
        , dataCon == kleE kle
            = pure E

        | Just (tyCon, [k, ty]) <- GHC.splitTyConApp_maybe ty0
        , GHC.eqType k GHC.liftedTypeKind
        , Just dataCon <- GHC.isPromotedDataCon_maybe tyCon
        , dataCon == kleS kle
            = S <$> go ty

        | Just (tyCon, [k, ty]) <- GHC.splitTyConApp_maybe ty0
        , GHC.eqType k GHC.liftedTypeKind
        , Just dataCon <- GHC.isPromotedDataCon_maybe tyCon
        , dataCon == kleV kle
            = return (V ty)

        | Just (tyCon, [k, a, b]) <- GHC.splitTyConApp_maybe ty0
        , GHC.eqType k GHC.liftedTypeKind
        , Just dataCon <- GHC.isPromotedDataCon_maybe tyCon
        , dataCon == kleAlt kle
            = (:\/) <$> go a <*> go b

        | Just (tyCon, [k, a, b]) <- GHC.splitTyConApp_maybe ty0
        , GHC.eqType k GHC.liftedTypeKind
        , Just dataCon <- GHC.isPromotedDataCon_maybe tyCon
        , dataCon == kleApp kle
            = (:<>) <$> go a <*> go b

#ifdef KLEENE_TOP
        | Just (tyCon, [k]) <- GHC.splitTyConApp_maybe ty0
        , GHC.eqType k GHC.liftedTypeKind
        , Just dataCon <- GHC.isPromotedDataCon_maybe tyCon
        , dataCon == kleT kle
            = pure T
#endif

        | otherwise = Left "regex argument is not a promoted RE"

-- | Elaborate type-level list (of types).
elaborateStr :: KleNames -> GHC.Type -> Either String [GHC.Type]
elaborateStr kle ty0
    | Just (tyCon, [k, x, t]) <- GHC.splitTyConApp_maybe ty0
    , GHC.eqType k GHC.liftedTypeKind
    , Just dataCon <- GHC.isPromotedDataCon_maybe tyCon
    , dataCon == GHC.consDataCon
        = do
            xs <- elaborateStr kle t
            return (x : xs)
    | Just (tyCon, [k]) <- GHC.splitTyConApp_maybe ty0
    , GHC.eqType k GHC.liftedTypeKind
    , Just dataCon <- GHC.isPromotedDataCon_maybe tyCon
    , dataCon == GHC.nilDataCon
        = Right []
    | otherwise
        = Left "string argument is not a type level list"
