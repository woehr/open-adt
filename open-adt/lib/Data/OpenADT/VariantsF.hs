-- |
-- Module      : Data.OpenADT.VariantsF
-- Copyright   : Copyright (c) Jordan Woehr, 2018
-- License     : BSD
-- Maintainer  : Jordan Woehr
-- Stability   : experimental
--
-- This module lifts functions from row-types on 'Var' to the 'VarF' type. All
-- functions in this module are named as their row-types version with an __F__
-- appended.

{-# Language AllowAmbiguousTypes #-}
{-# Language ConstraintKinds #-}
{-# Language FlexibleContexts #-}
{-# Language RankNTypes #-}
{-# Language ScopedTypeVariables #-}
{-# Language TypeApplications #-}
{-# Language TypeFamilies #-}
{-# Language TypeOperators #-}

module Data.OpenADT.VariantsF where

import           Control.Arrow                            ( (+++) )
import           Data.String                              ( IsString )
import           Data.Row
import           Data.Row.Variants
import           Data.Row.Internal                        ( Unconstrained1 )

import           Data.OpenADT.VarF

-- | Like 'diversify' but specialised for 'VarF'.
--
-- @since 1.0.0
diversifyF
  :: forall r' x r
   . (ApplyRow x r .\/ ApplyRow x r' ≈ ApplyRow x (r .\/ r'))
  => VarF r x
  -> VarF (r .\/ r') x
diversifyF = mapVarF $ diversify @(ApplyRow x r') @(ApplyRow x r)

-- | Like 'trial' but specialised for 'VarF'.
--
-- @since 1.0.0
trialF
  :: (ApplyRow x r .- l ≈ ApplyRow x (r .- l), KnownSymbol l)
  => VarF r x
  -> Label l
  -> Either (ApplyRow x r .! l) (VarF (r .- l) x)
trialF v l = (id +++ VarF) (trial (unVarF v) l)

-- | Like 'multiTrial' but specialised for 'VarF'.
--
-- @since 1.0.0
multiTrialF
  :: forall u v x
   . ( ApplyRow x v .\\ ApplyRow x u ≈ ApplyRow x (v .\\ u)
     , AllUniqueLabels (ApplyRow x u)
     , Forall (ApplyRow x (v .\\ u)) Unconstrained1
     )
  => VarF v x
  -> Either (VarF u x) (VarF (v .\\ u) x)
multiTrialF = (VarF +++ VarF) . multiTrial . unVarF

-- | Like 'erase' but specialised for 'VarF'.
--
-- @since 1.0.0
eraseF
  :: forall c r x b
   . Forall (ApplyRow x r) c
  => (forall a . c a => a -> b)
  -> VarF r x
  -> b
eraseF f = snd @String . eraseWithLabelsF @c f

-- | Like 'eraseWithLabels' but specialised for 'VarF'.
--
-- @since 1.0.0
eraseWithLabelsF
  :: forall c r x s b
   . (Forall (ApplyRow x r) c, IsString s)
  => (forall a . c a => a -> b)
  -> VarF r x
  -> (s, b)
eraseWithLabelsF f = eraseWithLabels @c f . unVarF

-- | Like 'caseon' but specialised for 'VarF'.
--
-- @since 1.0.0
caseonF :: (Switch (ApplyRow x v) r y) => Rec r -> VarF v x -> y
caseonF r = caseon r . unVarF

-- | Like 'switch' but specialised for 'VarF'.
--
-- @since 1.0.0
switchF :: (Switch (ApplyRow x v) r y) => VarF v x -> Rec r -> y
switchF v = switch (unVarF v)
