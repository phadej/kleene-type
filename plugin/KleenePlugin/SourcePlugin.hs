-- | Source plugin.
--
-- Transform @[[ a, b, c ]]@ into @a ':::' b ':::' c ':::' 'Nil'@.
module KleenePlugin.SourcePlugin (sourcePlugin) where

import           Control.Monad.IO.Class (MonadIO (..))
import qualified Data.Generics          as SYB
import qualified GhcPlugins             as GHC
import           HsExtension            (GhcPs, NoExt (..))
import           HsSyn
import           SrcLoc

debug :: MonadIO m => String -> m ()
-- debug = liftIO . putStrLn
debug _ = pure ()

sourcePlugin :: GHC.ModSummary -> GHC.HsParsedModule -> GHC.Hsc GHC.HsParsedModule
sourcePlugin _modSummary m = do
    dflags <- GHC.getDynFlags
    debug $ GHC.showPpr dflags (GHC.hpm_module m )
    hpm_module' <- transform dflags (GHC.hpm_module m)
    let module' = m { GHC.hpm_module = hpm_module' }
    return module'

transform
    :: GHC.DynFlags
    -> GHC.Located (HsModule GhcPs)
    -> GHC.Hsc (GHC.Located (HsModule GhcPs))
transform dflags = SYB.everywhereM (SYB.mkM transform') where
    transform' :: LHsExpr GhcPs -> GHC.Hsc (LHsExpr GhcPs)
    -- [[ x, y, z ]] --> x ::: y ::: z ::: Nil -- HList
    transform' (L l (ExplicitList _ Nothing [L l' (ExplicitList  _ Nothing exprs)]))
        | inside l l' = do
            debug $ "[[ I:  " ++ GHC.showPpr dflags exprs
            let L _ exprs' = foldr cons nil exprs
            debug $ "[[ O: " ++ GHC.showPpr dflags exprs'
            return $ L l exprs'
    -- ([ x, y, z ]) --> mkREList [[ x, y, z ]] -- REList
    transform' (L l (HsPar _ (L l' (ExplicitList  _ Nothing exprs))))
        | inside l l' = do
            debug $ "([ I: " ++ GHC.showPpr dflags exprs
            let exprs' = foldr cons nil exprs
            let L _ expr = mkREList (L l' (HsPar NoExt exprs'))
            debug $ "([ O: " ++ GHC.showPpr dflags expr
            return $ L l expr
    transform' (L l (HsPar _ (L l' (ExplicitTuple  _ targs GHC.Boxed))))
        | inside l l'
        , Just (f : exprs) <- traverse fromTupArg targs = do
            debug $ "(( I: " ++ GHC.showPpr dflags exprs
            debug $ "(( J: " ++ GHC.showPpr dflags f
            let exprs' = foldr cons nil exprs
            let expr   = mkREList (L l' (HsPar NoExt exprs'))
            let expr'  = HsApp NoExt f expr
            debug $ "(( O: " ++ GHC.showPpr dflags expr'
            return $ L l (HsPar NoExt (L l expr'))
    transform' expr =
        return expr

fromTupArg :: LHsTupArg id -> Maybe (LHsExpr id)
fromTupArg (L _ (Present _ e)) = Just e
fromTupArg _                   = Nothing

-------------------------------------------------------------------------------
-- HList constructors
-------------------------------------------------------------------------------

nil :: LHsExpr GhcPs
nil = L nss $ HsVar NoExt $ L nss nilRdrName where
    nilRdrName :: GHC.RdrName
    nilRdrName = GHC.mkRdrUnqual (GHC.mkDataOcc "Nil")

cons :: LHsExpr GhcPs -> LHsExpr GhcPs -> LHsExpr GhcPs
cons x xs = L nss $ OpApp NoExt x (L nss $ HsVar NoExt $ L nss consRdrName) xs where
    consRdrName :: GHC.RdrName
    consRdrName = GHC.mkRdrUnqual (GHC.mkDataOcc ":::")

mkREList :: LHsExpr GhcPs -> LHsExpr GhcPs
mkREList xs = L nss $ HsPar NoExt $ L nss $ HsApp NoExt (L nss $ HsVar NoExt $ L nss mkREListRdrName) xs where
    mkREListRdrName :: GHC.RdrName
    mkREListRdrName = GHC.mkRdrUnqual (GHC.mkVarOcc "mkREList")

nss :: SrcSpan
nss = GHC.noSrcSpan

-------------------------------------------------------------------------------
-- Location checker
-------------------------------------------------------------------------------

-- Check that spans are right inside each others, i.e. we match
-- that there are no spaces between parens and brackets
inside :: SrcSpan -> SrcSpan -> Bool
inside (RealSrcSpan a) (RealSrcSpan b) = and
    [ srcSpanStartLine a == srcSpanStartLine b
    , srcSpanEndLine a == srcSpanEndLine b
    , srcSpanStartCol a + 1 == srcSpanStartCol b
    , srcSpanEndCol a == srcSpanEndCol b + 1
    ]
inside _ _ = False
