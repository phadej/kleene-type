module KleenePlugin.Debug where

import qualified Outputable         as PP

import Debug.Trace

tracePpr :: PP.Outputable a => String -> a -> b -> b
tracePpr tag x = trace $ PP.showSDocUnsafe $ PP.hang (PP.text tag) 2 (PP.ppr x)

tracePprId :: PP.Outputable b => String -> b -> b
tracePprId tag x = tracePpr tag x x
