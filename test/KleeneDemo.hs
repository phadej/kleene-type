{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE TypeOperators    #-}
{-# OPTIONS_GHC -fplugin=KleenePlugin #-}
{-# OPTIONS_GHC -dcore-lint           #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
module Main where

import Kleene.Type
import Kleene.Type.Examples.KleeneSH

-------------------------------------------------------------------------------
-- Heterogenous list
-------------------------------------------------------------------------------

-- :t heterogenousList
heterogenousList = [[ True, 'x', "SmallFP" ]]































-------------------------------------------------------------------------------
-- REList
-------------------------------------------------------------------------------

exampleRelist = ([ True, 't', False, 'f' ]) :: REList (S (V Bool <> V Char))































-------------------------------------------------------------------------------
-- A Call
-------------------------------------------------------------------------------

exampleCall = (( find_, #type, #f, "plugin", "src" ))































-------------------------------------------------------------------------------
-- Error cases
-------------------------------------------------------------------------------

-- findError = (( find_, #type, #b, "plugin", "src" ))































-------------------------------------------------------------------------------
-- Unions
-------------------------------------------------------------------------------

charOrBool :: REList (V Char \/ V Bool) -> IO ()
charOrBool re = withREList re $ withUnion
    (withV print)
    (withV (print . not))

ex1 = (( charOrBool, 'a' ))
ex2 = (( charOrBool, True ))

-- err1 = (( charOrBool, "foobar" ))
-- err2 = (( charOrBool, 'a', True ))
-- err3 = (( charOrBool ))
-- err3b = charOrBool (mkREList Nil)































-------------------------------------------------------------------------------
-- Top
-------------------------------------------------------------------------------

#ifdef KLEENE_TOP
singleBool :: REList (T <> V Bool <> T) -> Bool
singleBool re = withREList re $ withAppend3 (\_ x _ -> x)
    (withTop ())
    (withV id)
    (withTop ())

ex3 = (( singleBool, 'a', 'b', 'c', True, 'x', "foo", Left 'l'))































-------------------------------------------------------------------------------
-- Haskelly
-------------------------------------------------------------------------------

singleBool' :: REList (T  <> V Bool <> T) -> Bool
singleBool' (REList m xs) = case haskelly m xs of
    (_, (b, _)) -> b

ex4 = (( singleBool, False ))
#endif































-------------------------------------------------------------------------------
-- Main
-------------------------------------------------------------------------------

main :: IO ()
main = return ()
