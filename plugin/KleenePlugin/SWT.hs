{-# LANGUAGE DeriveFunctor #-}
module KleenePlugin.SWT where

import Control.Monad (ap)

-- | Strict (list) writer monad.
newtype SWT w m a = SWT { unSWT :: ([w] -> [w]) -> m ([w] -> [w], a) }
  deriving Functor

runSWT :: Functor m => SWT w m a -> m ([w], a)
runSWT s = fmap (\(endo, a) -> (endo [], a)) (unSWT s id)

tellSingleSWT :: Monad m => w -> SWT w m ()
tellSingleSWT w = SWT $ \endo -> return ((w :) . endo, ())

liftSWT :: Functor m => m a -> SWT w m a
liftSWT m = SWT $ \endo -> fmap ((,) endo) m

instance Monad m => Applicative (SWT w m) where
    pure  = return
    (<*>) = ap

instance Monad m => Monad (SWT w m) where
    return x = SWT $ \endo -> return (endo, x)
    m >>= k = SWT $ \endo0 -> do
        (endo1, x) <- unSWT m endo0
        unSWT (k x) endo1
