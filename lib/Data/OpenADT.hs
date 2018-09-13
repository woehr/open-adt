-- | Module      : Data.OpenADT
--   Description : Short description
--   Copyright   : (c) Jordan Woehr, 2018
--   License     : BSD
--   Maintainer  : Jordan Woehr
--   Stability   : experimental
--   
--   Here is a longer description of this module, containing some
--   commentary with @some markup@.

module Data.OpenADT
  ( module Data.OpenADT
  , module Data.OpenADT.TH
  , module Data.OpenADT.VarF
  )
where

import           Data.Functor.Foldable                    ( Fix(..) )
import           Data.OpenADT.TH
import           Data.OpenADT.VarF

-- | A algebraic data type that can have constructors added and removed.
type OpenADT r = Fix (VarF r)
