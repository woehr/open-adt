-- | Description : Short description
--   
--   Here is a longer description of this module, containing some
--   commentary with @some markup@.

{-# Language ConstraintKinds #-}
{-# Language DataKinds #-}
{-# Language DeriveFunctor #-}
{-# Language FlexibleContexts #-}
{-# Language FlexibleInstances #-}
{-# Language InstanceSigs #-}
{-# Language MultiParamTypeClasses #-}
{-# Language OverloadedLabels #-}
{-# Language PatternSynonyms #-}
{-# Language RankNTypes #-}
{-# Language ScopedTypeVariables #-}
{-# Language TemplateHaskell #-}
{-# Language TypeApplications #-}
{-# Language TypeFamilies #-}
{-# Language TypeOperators #-}
{-# Language UndecidableInstances #-}
{-# Language ViewPatterns #-}

{-# OPTIONS_HADDOCK prune, show-extensions #-}

module Main where

import           Data.OpenADT

-- row-types
import           Data.Row
import           Data.Row.Variants 

-- recursion-schemes
import           Data.Functor.Foldable                    ( Fix(..)
                                                          , cata
                                                          )

-- deriving-compat
import           Text.Show.Deriving                       ( deriveShow1 )

-------------- Example --------------

-- We create three different data types corresponding to three constructors
-- of a variant.

data NilF x = NilF'
  deriving (Eq, Functor, Show)

data Cons1F a x = Cons1F' a x
  deriving (Eq, Functor, Show)

data Cons2F a x = Cons2F' a a x
  deriving (Eq, Functor, Show)

deriveShow1 ''NilF
deriveShow1 ''Cons1F
deriveShow1 ''Cons2F

mkVarPattern ''NilF   "nilF"   "Nil"   "NilF"
mkVarPattern ''Cons1F "cons1F" "Cons1" "Cons1F"

pattern Cons2F :: (OpenAlg r "cons2F" (Cons2F a) v) => a -> a -> v -> VarF r v
pattern Cons2F a b v <- VarF (view #cons2F -> Just (Cons2F' a b v))
  where Cons2F a b v = VarF (IsJust #cons2F (Cons2F' a b v))

pattern Cons2 :: (OpenAlg r "cons2F" (Cons2F a) (OpenADT r))
              => a -> a -> OpenADT r -> OpenADT r
pattern Cons2 a b v = Fix (Cons2F a b v)

-- Two example list types. Both use the same Nil and Cons types.
type List1RowF a = ("nilF"   .== NilF 
                  .+ "cons1F" .== Cons1F a
                   )
type List2RowF a = ( "nilF"   .== NilF
                  .+ "cons1F" .== Cons1F a
                  .+ "cons2F" .== Cons2F a
                   )

type List1F a =      VarF (List1RowF a)
type List1  a = Fix (VarF (List1RowF a))

type List2F a = VarF    (List2RowF a)
type List2  a = OpenADT (List2RowF a) -- OpenADT r = Fix (VarF r)

class OverList a a' r (f :: * -> *) where
  fmapList' :: (a -> a') -> f (OpenADT r) -> OpenADT r

instance (OpenAlg r "nilF" NilF (OpenADT r)) => OverList a a' r NilF where
  fmapList' _ NilF' = Nil

instance ( OpenAlg r "cons1F" (Cons1F a') (OpenADT r)
         ) => OverList a a' r (Cons1F a) where
  fmapList' f (Cons1F' a x) = Cons1 (f a) x

instance ( OpenAlg r "cons2F" (Cons2F a') (OpenADT r)
         ) => OverList a a' r (Cons2F a) where
  fmapList' f (Cons2F' a b x) = Cons2 (f a) (f b) x

instance (Forall r (OverList a a' s)) => OverList a a' s (VarF r) where
  fmapList' f =
    varFAlg @r @(OverList a a' s) @(OpenADT s) @(OpenADT s) (fmapList' f)

fmapList :: (Forall r Functor, OverList a a' s (VarF r))
         => (a -> a') -> OpenADT r -> OpenADT s
fmapList f = cata (fmapList' f)

altFmapList :: forall a a' r s.
            ( Forall r Functor
            , Forall r (OverList a a' s)
            )
            => (a -> a') -> OpenADT r -> OpenADT s
altFmapList f = cata $
  varFAlg @r @(OverList a a' s) @(OpenADT s) @(OpenADT s) (fmapList' f)

main :: IO ()
main = do
  -- Cons and Nil can be used in different types
  let l1 = Cons1 0 (Cons1 1 Nil) :: List1 Int
  print l1
  -- > Fix (VarF (ConsF' 0 (Fix (VarF (ConsF' 1 (Fix (VarF NilF')))))))

  -- We can use recursion schemes over the structures to change them. In this
  -- example, a List is changed to a List2
  let l1' =
        cata
          ( Fix
          . mapVarF (diversify @("cons2F" .== Cons2F Int (List2 Int)))
          ) l1 :: List2 Int
  print l1'
  -- > Fix (VarF (ConsF' 0 (Fix (VarF (ConsF' 1 (Fix (VarF NilF')))))))

  let l2 = Cons2 2 3 (Cons1 4 Nil) :: List2 Int
  print l2
  -- > Fix (VarF (Cons2F' 2 3 (Fix (VarF (ConsF' 4 (Fix (VarF NilF')))))))

  let l2' = cata alg l2 :: List1 Int
       where alg NilF = Nil
             alg (Cons1F a x) = Cons1 a x
             alg (Cons2F a b x) = Cons1 a (Cons1 b x)
             alg _ = error "GHC will complain about incomplete patterns even \
                           \though all cases are covered."
  print l2'

  let l3 = Cons1 42 Nil :: List1 Int
  -- The type class approach will not generate incomplete pattern warnings.
  -- GHC will error if an instance is missing.
  print (   fmapList (show @Int) l3 :: List1 String)
  print (altFmapList (show @Int) l3 :: List1 String)
  let l3' :: List1 String
      l3' = cata f l3
        where f :: List1F Int (List1 String) -> List1 String
              -- Another alternative that does not produce incomplete pattern
              -- warnings is to use the caseon/switch functions from row-types,
              -- which requires a record of functions that matches exactly the
              -- constructors of the variant.
              f = caseon r . unVarF
              r = (  #nilF   .== (\NilF' -> Nil)
                  .+ #cons1F .== (\(Cons1F' a x) -> Cons1 (show @Int a) x)
                  )
  print l3'
