module KleenePlugin (plugin) where

import qualified GhcPlugins                as GHC
import           KleenePlugin.SourcePlugin
import           KleenePlugin.TcPlugin

-- | The "KleenePlugin" does two things:
--
-- * It's a source plugin, transforming
--
--     @
--     [[ a, b, c, d, e ]]
--     @
--
--     into
--
--     @
--     (a ::: b ::: c ::: d ::: e ::: Nil)
--     @
--
--     this helps writing 'HList' more concisely.
--
--     Also @([ a, b, c ])@ is converted to @mkREList [[ a, b, c ]]@
--     and @(( f, a, b, c ))@ to @f ([ a, b, c ])@.
--     This let us write very lispy programs.
--
-- * Also it solves 'MatchI' constraints, when regular expression and
--     type list are fully determined.
--
--     So you can tell GHC to 'justMatchIt' (like with @justDoIt@ from [ghc-justdoit](http://hackage.haskell.org/package/ghc-justdoit)), instead of writing
--     the evidence proofs by hand.
--
-- To use plugin add following lines to the top of the source file:
--
-- @
-- {-\# OPTIONS_GHC -fplugin=KleenePlugin #-}
-- {-\# OPTIONS_GHC -dcore-lint           #-}
-- @
--
-- Enabling @-dcore-lint@ is very good idea. "KleenePlugin" is very experimental.
--
plugin :: GHC.Plugin
plugin = GHC.defaultPlugin
    { GHC.parsedResultAction = const sourcePlugin
    , GHC.tcPlugin           = const $ Just tcPlugin
    , GHC.pluginRecompile    = GHC.flagRecompile
    }
