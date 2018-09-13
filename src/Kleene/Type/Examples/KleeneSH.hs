{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeOperators         #-}
-- | This module defines \"type-safe\" bindings to some
-- of the UNIX shell tools.
--
-- We demonstrate the use of "Kleene.Type" (and "KleenePlugin")
-- to program in Haskell in completely structural way (i.e. non-nominal).
--
-- /Disclaimer:/ the fact that we __can__ doesn't mean that we __should__.
--
-- We may define self-proxy types instead of using 'K' for flags.
-- Then the usage will be more nice.
-- However, we don't, to emphasise the point, as in this module we only use
-- three types:
--
-- * 'REList' - lists
-- * 'String' - strings (for 'FilePath')
-- * 'K' - symbols \/ keywords
--
-- == Example
--
-- @
-- {-\# LANGUAGE DataKinds                #-}
-- {-\# LANGUAGE OverloadedLabels         #-}
-- {-\# OPTIONS_GHC -fplugin=KleenePlugin #-}
-- {-\# OPTIONS_GHC -dcore-lint           #-}
-- module Main (main) where
--
-- import "Kleene.Type.Examples.KleeneSH"
--
-- main :: IO ()
-- main = do
--     (( ls_, \#l, ".", \#h ))
--     (( find_, \#type, \#f, "plugin", "src" ))
-- @
--
-- We get very close to the dynamic feeling, compare to:
--
-- @
-- (do
--   (ls :l "." :h)
--   (ls :type :f "plugin" "src"))
-- @
--
module Kleene.Type.Examples.KleeneSH (
    -- * Commands
    -- ** ls
    ls_,
    LS,

    -- ** find
    find_,
    FIND, FIND', TYPES,

#ifdef KLEENE_TOP
    -- ** true
    true_,
    TRUE,
#endif

    -- * Implementation
    command,
    Flag,
    ToArg (..),

    -- * Re-exports
    module Kleene.Type,
    ) where

import Data.Either          (partitionEithers)
import Data.Proxy           (Proxy (..))
import GHC.TypeLits         (KnownSymbol)
import Kleene.Type
import System.Process       (readProcess)

-------------------------------------------------------------------------------
-- Commands
-------------------------------------------------------------------------------

-- | @ls@ - list directory contents.
ls_ :: REList LS -> IO ()
ls_ = command "ls"

type LS = S (V FilePath \/ Flag "l" \/ Flag "h")

#ifdef KLEENE_TOP
-- | @true@ - do nothing, successfully
true_ :: REList TRUE -> IO ()
true_ = command "true"

type TRUE = T
#endif

-- | @find@ - search for files in a directory hierarchy
find_ :: REList FIND -> IO ()
find_ (REList match argv) = do
    putStrLn $ ">>> " ++ cmd ++ " " ++ unwords args
    out <- readProcess cmd args ""
    putStr out
  where
    cmd = "find"
    args = fromFindArgs fargs

    fargs = map f (haskelly match argv)

    -- process argument
    f (Left fp)                        = FindDir fp
    f (Right (Left  (Key, fp)))        = FindName fp
    f (Right (Right (Key, Right Key))) = FindType "d"
    f (Right (Right (Key, Left Key)))  = FindType "f"

{-
    f' :: Match FIND' ys -> HList ys -> FindArg
    f' = withUnion (withV FindDir)
        $ withUnion (withAppend ($) (withV (const FindName)) (withV id))
        $            withAppend ($) (withV (const FindType))
            $ withUnion (withV kVal) (withV kVal)
-}

data FindArg
    = FindDir  FilePath
    | FindName String
    | FindType String

fromFindArgs :: [FindArg] -> [String]
fromFindArgs fargs = dirs ++ concat args where
    (dirs, args) = partitionEithers (fmap f fargs)

    f (FindDir d)  = Left d
    f (FindName n) = Right ["-name", n]
    f (FindType d) = Right ["-type", d]

type FIND  = S FIND'
type FIND' = V FilePath \/ Flag "name" <> V FilePath \/ Flag "type" <> TYPES
type TYPES = Flag "d" \/ Flag "f"

-------------------------------------------------------------------------------
-- Implementation
-------------------------------------------------------------------------------

type Flag s = V (Key s)

-- | This is blunt command, we don't really need regular expression
-- here as we quite simplfy flatten the the 'HList'.
--
-- See 'find_' for more sophisticated example.
command
    :: forall re. REInductionC ToArg re
    => FilePath -- ^ executable
    -> REList re -- ^ arguments
    -> IO ()
command cmd (REList match argv) = do
    putStrLn $ ">>> " ++ cmd ++ " " ++ unwords (flags ++ args)
    out <- readProcess cmd (flags ++ args) ""
    putStr out
  where
    (flags, args) = partitionEithers $ unAux (reInductionC (Proxy :: Proxy ToArg)
        e v a l r n c
#ifdef KLEENE_TOP
        top
#endif
        match)
        argv

    e = Aux $ \Nil -> []
    v :: ToArg x => Aux '[x]
    v = Aux $ \(x ::: Nil) -> [toArg x]
    a xs' f g = Aux $ \zs -> case split xs' zs of
        (xs, ys) -> unAux f xs ++ unAux g ys
    l = id
    r = id
    n = e
    c = a

#ifdef KLEENE_TOP
    top _ = Aux $ const [] -- top matches omitted arguments
#endif

newtype Aux xs = Aux { unAux :: HList xs -> [Either String String] }

-- | Convert @a@ to 'String' cli-argument.
class ToArg a where
    toArg :: a -> Either String String

-- | 'String' is "good" argument, this is also 'FilePath' instance.
instance c ~ Char => ToArg [c] where
    toArg = Right

-- | Prepends the '-' character.
instance KnownSymbol s => ToArg (Key s) where
    toArg = Left . ('-' :) . keyVal
