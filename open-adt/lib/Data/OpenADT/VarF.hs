-- |
-- Module      : Data.OpenADT.VarF
-- Copyright   : Copyright (c) Jordan Woehr, 2018-2019
-- License     : BSD
-- Maintainer  : Jordan Woehr
-- Stability   : experimental
--
-- This module defines the 'VarF' type and related functions and instances.
-- This type wraps a variant of types that have all had the same type applied
-- to them. Most often this will be a variant constructed with a row of
-- functors.

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.OpenADT.VarF where

import           Control.Arrow                            ( (+++) )
import           Data.Constraint
import           Data.Functor.Classes
import           Data.Functor.Const
import           Data.Functor.Product
import           Data.Proxy
import           Data.Row
import           Data.Row.Internal
import           Data.Row.Variants

-- | Apply a type to a 'Row'.
type family ApplyRow (x :: *) (r :: Row (* -> *)) :: Row * where
  ApplyRow x ('R lt) = 'R (ApplyLT x lt)

-- | Apply a type to each element of an 'LT'.
type family ApplyLT (x :: *) (r :: [LT (* -> *)]) :: [LT *] where
  ApplyLT _ '[] = '[]
  ApplyLT x (l ':-> f ': fs) = ((l ':-> f x) ': ApplyLT x fs)

-- | A newtype that wraps a variant. The variant is a row made up of
--   __(* -> *)__ that all have the type __x__ applied to them with 'ApplyRow'.
newtype VarF (r :: Row (* -> *)) x = VarF { unVarF :: Var (ApplyRow x r) }

deriving instance Forall (ApplyRow x r) Eq => Eq (VarF r x)
deriving instance (Forall (ApplyRow x r) Eq, Forall (ApplyRow x r) Ord) => Ord (VarF r x)
deriving instance Forall (ApplyRow x r) Show => Show (VarF r x)

-- | A helper for writing functions with 'metamorph''. This type reverses the
--   argument order of 'VarF' so the 'Row' parameter is last.
newtype VarF' x (r :: Row (* -> *)) = VarF' { unVarF' :: Var (ApplyRow x r) }

-- | A helper for writing functions with 'metamorph''. This type wraps an
--   __f a__ but takes the type arguments in the order __a f__.
newtype FlipApp (a :: *) (f :: * -> *) = FlipApp (f a)

-- | Apply a function to the variant within a 'VarF'.
--
-- @since 1.0
mapVarF :: (Var (ApplyRow x u) -> Var (ApplyRow x v)) -> VarF u x -> VarF v x
mapVarF f (VarF v) = VarF (f v)

-- | This function is useful for implementing functions that are used as
--   catamorphisms, and sometimes 'VarF' instances. The function applies its
--   first argument to whatever variant is wrapped by __VarF r x__ provided all
--   elements of the row __r__ are constrained by __c__.
--
--   For an example, see the 'Show1' instance implementation.
--
-- @since 1.0
varFAlg
  :: forall (c :: (* -> *) -> Constraint) (r :: Row (* -> *)) (x :: *) (y :: *)
   . (Forall r c)
  => (forall f . (c f) => f x -> y)
  -> VarF r x
  -> y
varFAlg f =
  getConst
    . metamorph' @_ @r @c @(VarF' x) @(Const y) @(FlipApp x) Proxy
                                                             doNil
                                                             doUncons
                                                             doCons
    . VarF'
    . unVarF
 where
  doNil = impossible . unVarF'

  doUncons l = (FlipApp +++ VarF') . flip trial l . unVarF'

  doCons
    :: forall ℓ τ ρ
     . (c τ)
    => Label ℓ
    -> Either (FlipApp x τ) (Const y ( 'R ρ))
    -> Const y ( 'R (ℓ ':-> τ ': ρ))
  doCons _ (Left  (FlipApp v)) = Const (f v)
  doCons _ (Right (Const   y)) = Const y

-- | The same as 'varFAlg', but with the constraint fixed to 'Unconstrained1'.
--
-- @since 1.0
varFAlg'
  :: forall (r :: Row (* -> *)) (x :: *) (y :: *)
   . (Forall r Unconstrained1)
  => (forall f . (Unconstrained1 f) => f x -> y)
  -> VarF r x
  -> y
varFAlg' = varFAlg @Unconstrained1 @r @x @y

-- | RowFromTo fs b := for (l,a) in fs; SUM [ l :-> (a -> b) ]
type family RowFromTo (a :: Row *) (b :: *) :: Row * where
  RowFromTo ('R r) b = 'R (RowFromToR r b)

-- | 'RowFromTo' over a list of 'LT'.
type family RowFromToR (a :: [LT *]) (b :: *) :: [LT *] where
  RowFromToR '[] x = '[]
  RowFromToR (l ':-> a ': rs) b = l ':-> (a -> b) ': RowFromToR rs b

-- | Given a record of functions, use those functions to remove the
-- corresponding rows from the input. Type errors will ensue if the record
-- contains fields of the output variant.
--
-- @since 1.0
reduceVarF
  :: forall r s t x r' s' t'
   . ( t ≈ r .\\ s
     , r' ~ ApplyRow x r
     , s' ~ ApplyRow x s
     , s' ≈ r' .\\ t'
     , t' ≈ r' .\\ s'
     , Disjoint s' t'
     , Switch t' (RowFromTo t' (VarF s x)) (VarF s x)
     )
  => Rec (RowFromTo t' (VarF s x))
  -> VarF r x
  -> VarF s x
reduceVarF f (VarF v) = case multiTrial @t' @r' v of
  Left  x -> caseon f x
  Right x -> VarF x

-- |
--
-- @since 1.0
instance Forall r Functor => Functor (VarF r) where
  fmap :: forall a b. (a -> b) -> VarF r a -> VarF r b
  fmap f = VarF . unVarF' . go . VarF' . unVarF

    where
      go = metamorph' @_ @r @Functor @(VarF' a) @(VarF' b) @(FlipApp a)
             Proxy doNil doUncons doCons

      doNil = impossible . unVarF'

      doUncons l = (FlipApp +++ VarF') . flip trial l . unVarF'

      doCons :: forall l f s. (KnownSymbol l, Functor f)
             => Label l
             -> Either (FlipApp a f) (VarF' b ('R s))
             -> VarF' b ('R (l ':-> f ': s))
      doCons l (Left (FlipApp x)) = VarF' $ unsafeMakeVar l $ f <$> x
      doCons _ (Right (VarF' v)) = VarF' $ unsafeInjectFront v

-- |
--
-- @since 1.0
instance Forall r Eq1 => Eq1 (VarF r) where
  liftEq :: forall a b. (a -> b -> Bool) -> VarF r a -> VarF r b -> Bool
  liftEq f (VarF x) (VarF y) = getConst $ metamorph' @_ @r @Eq1
      @(Product (VarF' a) (VarF' b)) @(Const Bool) @(Const Bool)
      Proxy doNil doUncons doCons (Pair (VarF' x) (VarF' y))

    where doNil :: Product (VarF' a) (VarF' b) Empty
                -> Const Bool (Empty :: Row (* -> *))
          doNil (Pair (VarF' z) _) = Const (impossible z)

          doUncons :: forall ℓ τ ρ. (KnownSymbol ℓ, Eq1 τ)
                   => Label ℓ
                   -> Product (VarF' a) (VarF' b) ('R (ℓ ':-> τ ': ρ))
                   -> Either (Const Bool τ)
                             (Product (VarF' a) (VarF' b) ('R ρ))
          doUncons l (Pair (VarF' r1) (VarF' r2)) =
            case (trial r1 l, trial r2 l) of
              (Left u, Left v)   -> Left $ Const $ liftEq f u v
              (Right u, Right v) -> Right $ Pair (VarF' u) (VarF' v)
              _                  -> Left $ Const False

          doCons :: forall ℓ (τ :: * -> *) ρ
                  . Label ℓ
                 -> Either (Const Bool τ) (Const Bool ('R ρ))
                 -> Const Bool ('R (ℓ ':-> τ ': ρ))
          doCons _ (Left (Const w))  = Const w
          doCons _ (Right (Const w)) = Const w

-- |
--
-- @since 1.1
instance (Forall r Eq1, Forall r Ord1) => Ord1 (VarF r) where
  liftCompare :: forall a b. (a -> b -> Ordering) -> VarF r a -> VarF r b -> Ordering
  liftCompare f (VarF x) (VarF y) = getConst $ metamorph' @_ @r @Ord1
      @(Product (VarF' a) (VarF' b)) @(Const Ordering) @(Const Ordering)
      Proxy doNil doUncons doCons (Pair (VarF' x) (VarF' y))
    where doNil :: Product (VarF' a) (VarF' b) Empty -> Const Ordering Empty
          doNil (Pair (VarF' z) _) = Const (impossible z)

          doUncons :: forall ℓ τ ρ. (KnownSymbol ℓ, Ord1 τ)
                   => Label ℓ
                   -> Product (VarF' a) (VarF' b) ('R (ℓ ':-> τ ': ρ))
                   -> Either (Const Ordering τ)
                             (Product (VarF' a) (VarF' b) ('R ρ))
          doUncons l (Pair (VarF' r1) (VarF' r2)) =
            case (trial r1 l, trial r2 l) of
              (Left u,  Left v)  -> Left $ Const $ liftCompare f u v
              (Left _,  Right _) -> Left $ Const LT
              (Right _, Left _)  -> Left $ Const GT
              (Right u, Right v) -> Right $ Pair (VarF' u) (VarF' v)

          doCons :: forall ℓ (τ :: * -> *) ρ
                  . Label ℓ
                 -> Either (Const Ordering τ) (Const Ordering ('R ρ))
                 -> Const Ordering ('R (ℓ ':-> τ ': ρ))
          doCons _ (Left (Const w))  = Const w
          doCons _ (Right (Const w)) = Const w

-- |
--
-- @since 1.0
instance Forall r Show1 => Show1 (VarF r) where
  liftShowsPrec ::
    forall a. (Int -> a -> ShowS) -> ([a] -> ShowS) -> Int -> VarF r a -> ShowS
  liftShowsPrec sa sl p =
    let f :: forall f. (Show1 f) => f a -> ShowS
        f x = showParen (p > 10) (showString "VarF " . liftShowsPrec sa sl p x)
    in varFAlg @Show1 @r @a @ShowS f

-- | A type constraint synonym for convenience that can be used in, for
--   example, patterns. The variables __r__ (representing a Row) and __v__
--   (representing the type applied to __f__) are generally left abstract. The
--   variable __l__ is the label corresponding to __f v__.
--
--   The order of variables are in the same order as the equality constraint
--   in the synonym, making it easy to remember.
--
-- @since 1.0
type OpenAlg r l f v = ( ApplyRow v r .! l ≈ f v
                       , AllUniqueLabels (ApplyRow v r)
                       )
