{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE OverloadedLabels #-}
{-# OPTIONS_GHC -fplugin=KleenePlugin #-}
{-# OPTIONS_GHC -dcore-lint           #-}
module Main (main) where

import Kleene.Type.Examples.KleeneSH

main :: IO ()
main = do
    (( ls_, "." ))
    (( ls_, #l, "." ))
    (( ls_, #l, ".", #h ))
    (( find_, #type, #f, "plugin", "src" ))
    -- DEMO: Try changing #f to #g

#ifdef KLEENE_TOP
    true_ (mkREList Nil)
    (( true_, 'a', 'b', 'c' ))
#endif
