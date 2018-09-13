module KleenePlugin.Names where

import qualified Class      as GHC (Class)
import qualified GhcPlugins as GHC

-- | "State" of the type-checker plugin.
--
-- When initialising the plugin, we lookup names from "Kleene.Type".
data KleNames = KleNames
    { kleCls   :: !GHC.Class
    -- RE
    , kleRe    :: !GHC.TyCon
    , kleE     :: !GHC.DataCon
    , kleV     :: !GHC.DataCon
    , kleApp   :: !GHC.DataCon
    , kleAlt   :: !GHC.DataCon
    , kleS     :: !GHC.DataCon
#ifdef KLEENE_TOP
    , kleT     :: !GHC.DataCon
#endif
    -- Match
    , kleME    :: !GHC.DataCon
    , kleMV    :: !GHC.DataCon
    , kleMA    :: !GHC.DataCon
    , kleML    :: !GHC.DataCon
    , kleMR    :: !GHC.DataCon
    , kleMN    :: !GHC.DataCon
    , kleMC    :: !GHC.DataCon
#ifdef KLEENE_TOP
    , kleMT    :: !GHC.DataCon
#endif
    -- SList
    , kleSNil  :: !GHC.DataCon
    , kleSCons :: !GHC.DataCon
    -- Append
    , kleFApp  :: !GHC.TyCon
    -- Label
    , kleLabel :: !GHC.Class
    -- Key
    , kleKey   :: !GHC.TyCon
    }
