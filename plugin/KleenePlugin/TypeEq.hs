{-# LANGUAGE DeriveTraversable   #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE ScopedTypeVariables #-}
module KleenePlugin.TypeEq where

import Control.Monad.EitherK            (EitherKT, runEitherKT)
import Control.Monad.Trans.Class        (lift)
import Control.Monad.Trans.State.Strict (StateT (..), get, put)
import Control.Unification              (UTerm (..), applyBindingsAll, unify)
import Control.Unification.IntVar
       (IntBindingT, IntVar (..), evalIntBindingT)
import Control.Unification.Types
       (BindingMonad (..), UFailure (..), Unifiable (..))
import Data.Bifunctor                   (first)
import Data.Either                      (isRight)
import Data.Functor.Identity            (Identity, runIdentity)
import Data.Traversable                 (for)

import qualified Data.Map.Strict as Map
import qualified GhcPlugins      as GHC
import qualified Outputable      as PP

-- import KleenePlugin.Debug
import KleenePlugin.Names

maybeEqType
    :: KleNames                          -- ^ Names (only Key is used)
    -> Map.Map GHC.TyVar GHC.FastString  -- ^ IsLabel map
    -> GHC.Type -> GHC.Type
    -> Either UnifResult Bool
maybeEqType kle labels x y
    | GHC.eqType x y = Right True
{-
    | Just v   <- GHC.getTyVar_maybe y
    , Just str <- Map.lookup v labels
        = tracePpr "label?" (x,y,str) $ Right False
-}
    | mayUnify x' y' = Left (MayUnify x' y')
    | otherwise      = Right False
  where
    x' = elaborateType kle labels x
    y' = elaborateType kle labels y

data UnifResult = MayUnify (UTerm Mono GHC.TyVar) (UTerm Mono GHC.TyVar)

-------------------------------------------------------------------------------
--
-------------------------------------------------------------------------------

elaborateType :: KleNames -> Map.Map GHC.TyVar GHC.FastString -> GHC.Type -> UTerm Mono GHC.TyVar
elaborateType kle labels = go where
    go t
        | Just (tycon, [x]) <- GHC.splitTyConApp_maybe t
        , tycon == kleKey kle
        , Just sym <- GHC.isStrLitTy x =
            UTerm (MonoSym sym)
        | Just (f, x) <- GHC.splitAppTy_maybe t =
            UTerm $ MonoApp (go f) (go x)
        | Just tyvar <- GHC.getTyVar_maybe t =
            case Map.lookup tyvar labels of
                Nothing  -> UVar tyvar
                Just sym -> UTerm (MonoSym sym)
        | otherwise = UTerm (MonoC t)

data Mono a
    = MonoC GHC.Type         -- ^ concrete type
    | MonoApp a a            -- ^ application
    | MonoSym GHC.FastString -- ^ either @IsLabel sym a => a@ or @Key sym@
  deriving (Functor, Foldable, Traversable)

instance Unifiable Mono where
    zipMatch (MonoC a)      (MonoC b) | GHC.eqType a b = Just $ MonoC a
    zipMatch (MonoApp f x ) (MonoApp f' x') = Just $ MonoApp
        (Right (f, f'))
        (Right (x, x'))
    zipMatch (MonoSym sym)  (MonoSym sym') | sym == sym' = Just (MonoSym sym)
    zipMatch _ _ = Nothing

type M = EitherKT (UFailure Mono IntVar) (IntBindingT Mono Identity)

newtype UF = UF (UFailure Mono IntVar)

manyMayUnify :: [UnifResult] -> Either UF ()
manyMayUnify unifResults
    = first UF
    $ runIdentity
    $ evalIntBindingT
    $ runEitherKT action
  where
    action :: M ()
    action = do
        (xs, _vars) <- flip runStateT Map.empty $ for unifResults $ \ur ->
            case ur of
                MayUnify x y -> do
                    x' <- traverse makeVar x
                    y' <- traverse makeVar y
                    return (x', y')
        unified <- for xs $ \(x, y) -> unify x y
        _ <- applyBindingsAll unified
        return ()

    makeVar :: Ord a => a -> StateT (Map.Map a IntVar) M IntVar
    makeVar var = do
        m <- get
        case Map.lookup var m of
            Just iv -> return iv
            Nothing -> do
                iv <- lift (lift freeVar)
                put (Map.insert var iv m)
                return iv

mayUnify :: UTerm Mono GHC.TyVar -> UTerm Mono GHC.TyVar -> Bool
mayUnify x y = isRight $ manyMayUnify [MayUnify x y]

-------------------------------------------------------------------------------
-- Outputable
-------------------------------------------------------------------------------

instance PP.Outputable UF where
    ppr (UF (OccursFailure _v _t)) = PP.text "Occurs failure: "
    ppr (UF (MismatchFailure a b)) =
        PP.text "Couldn't match types" PP.<+>
        pprMono 0 a PP.<+>
        PP.text "and" PP.<+>
        pprMono 0 b

pprMono :: Rational ->  Mono (UTerm Mono IntVar) -> PP.SDoc
pprMono d (MonoC t)     = PP.pprPrec d t
pprMono _ (MonoSym sym) = PP.char '#' PP.<> PP.ppr sym
pprMono d (MonoApp f x) = PP.cparen (d > 10) $ pprMono' 10 f PP.<+> pprMono' 11 x

pprMono' :: Rational -> UTerm Mono IntVar -> PP.SDoc
pprMono' _ (UVar (IntVar v)) = PP.char '?' PP.<> PP.int v
pprMono' d (UTerm t)         = pprMono d t
