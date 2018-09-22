-- |
-- Module      : Data.OpenADT
-- Copyright   : Copyright (c) Jordan Woehr, 2018
-- License     : BSD
-- Maintainer  : Jordan Woehr
-- Stability   : experimental
--
-- This module defines the 'OpenADT' type, which is an algebraic data type
-- with constructors defined by its argument's row type.
--
-- Re-exports "Data.OpenADT.VarF" and "Data.OpenADT.TH".

module Data.OpenADT
  ( module Data.OpenADT
  , module Data.OpenADT.TH
  , module Data.OpenADT.VarF
  , module Data.OpenADT.VariantsF
  )
where

import           Data.Functor.Foldable                    ( Fix(..) )
import           Data.OpenADT.TH
import           Data.OpenADT.VarF
import           Data.OpenADT.VariantsF

-- | A algebraic data type that can have constructors added and removed.
type OpenADT r = Fix (VarF r)
