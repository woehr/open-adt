-- | Description : A short tutorial with code.

{-# Language ConstraintKinds #-}
{-# Language CPP #-}
{-# Language DataKinds #-}
{-# Language DeriveFunctor #-}
{-# Language FlexibleContexts #-}
{-# Language FlexibleInstances #-}
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

{-# OPTIONS_HADDOCK show-extensions #-}

module Data.OpenADT.Tutorial where

import           Data.OpenADT

#if !(MIN_VERSION_base(4,11,0))
import           Data.Semigroup                           ( (<>) )
#endif

-- row-types
import           Data.Row
import           Data.Row.Variants

-- recursion-schemes
import           Data.Functor.Foldable                    ( Fix(..)
                                                          , cata
                                                          )

-- deriving-compat
import           Text.Show.Deriving
import           Data.Eq.Deriving

-- * Introduction
--
-- $introduction
-- This module demonstrates how to create open algebraic data types (ADT), and
-- is intended to be read top-to-bottom. Throughout this tutorial, we will
-- create two different list types, 'List1' and 'List2', that share two of
-- their constructors. We will also see various ways that our structures can be
-- traversed and modified.
--
-- Note that several extensions are used, which should show up in the Haddock
-- generated documentation. In particular, I recommend being familiar with
-- OverloadedLabels and TypeApplications, otherwise some syntax may be
-- confusing.

-- | A type alias to reduce typing when writing the types of algebras.
type Alg f x = f x -> x

-- * Constructors
--
-- $constructors
-- The first step is to create data types that correspond to the constructors
-- of the types we want. We create three different types corresponding to
-- three list constructors: 'NilF', 'Cons1F', 'Cons2F'.
--
-- For example, a two elements cons, 'Cons2F', is defined as:
--
-- @
-- -- | A two element cons element.
-- data Cons2F a x = Cons2F' a a x
--   deriving (Eq, Functor, Show)
-- @
--
-- Note that the recursion of the structure is expressed in the type variable
-- @x@ rather than explicitly. The constructor should also be a functor.
--
-- For convenience we can use 'deriveShow1' from "Text.Show.Deriving" to derive
-- 'Show1' instances (and 'deriveEq1' from "Data.Eq.Deriving" for 'Eq1' if
-- desired).
--
-- @
-- 'deriveShow1' ''Cons2F
-- @

-- | The base case of a list type.
data NilF x = NilF'
  deriving (Eq, Functor, Show)

-- | A one element cons element.
data Cons1F a x = Cons1F' a x
  deriving (Eq, Functor, Show)

-- | A two element cons element.
data Cons2F a x = Cons2F' a a x
  deriving (Eq, Functor, Show)

deriveEq1 ''NilF
deriveEq1 ''Cons1F
deriveEq1 ''Cons2F

deriveShow1 ''NilF
deriveShow1 ''Cons1F
deriveShow1 ''Cons2F

-- * Rows
--
-- $rows
-- With constructors defined, we can define type synonyms that describe how
-- constructors are combined to create an ADT. These synonyms
-- are 'Row's, which are lists of labels (given by type-level strings) with
-- corresponding types. The type operator ('.==') is used to associate a label
-- with its type, the result of which is a row; ('.+') is used to combine two
-- rows into a new row. These operators, and the 'Row' type, are defined in
-- the row-types package.

-- | The row of the first list type. It defines a \"standard\" list type.
type List1RowF a = ( "nilF"   .== NilF
                  .+ "cons1F" .== Cons1F a
                   )

-- | The row of the second list type. This type re-uses the constructors of
-- 'List1RowF' and includes a third constructor: a two element cons.
type List2RowF a = ( "nilF"   .== NilF
                  .+ "cons1F" .== Cons1F a
                  .+ "cons2F" .== Cons2F a
                   )

-- * Types
--
-- $types
-- The 'VarF' newtype forms the basis of an open ADT. It wraps the variant
-- whose possible values are the constructors of the ADT. Its type constructor
-- takes two parameters:
--
-- - a row of types with the kind @(* -> *)@,
-- - and a type of kind @(*)@ that is applied to each element of the row.
--
-- 'VarF' has a functor instance when all the types of the row are functors.
-- Using 'VarF' we can define the base functor of our ADTs. Taking the fixpoint
-- of these functor types yields the ADT.

-- | The base functor of the 'List1' type. It is a 'VarF' with the row
-- 'List1RowF'.
type List1F a = VarF (List1RowF a)

-- | A list type. We obtain this type by taking the fixed point of its base
-- functor.
type List1  a = Fix (VarF (List1RowF a))

-- | The base functor of the 'List2' type.
type List2F a = VarF (List2RowF a)

-- | A list type with a two element cons. This type is defined with the
-- 'OpenADT' synonym, which is simply conveinience for @Fix (VarF r)@.
type List2  a = OpenADT (List2RowF a)

-- * Patterns
--
-- $patterns
-- In order to simplify our code, and avoid using 'VarF' directly, we can
-- define pattern synonyms for each constructor. Importantly, if written
-- generically enough, these patterns will work for a constructor regardless
-- the specific type it is used in. For example, we can write a single pattern
-- that matches the 'NilF' constructor in both the 'List1' and 'List2' types!
-- This is achieved with the pattern below:
--
-- @
-- pattern NilF :: (OpenAlg r "nilF" NilF x) => VarF r x
-- pattern NilF \<- VarF ('view' #nilF -\> Just NilF')
--   where NilF = VarF ('IsJust' #nilF NilF')
-- @
--
-- Note that in 'NilF', the variables @r@ and @x@ are left abstract. This
-- allows any row and type to be used with the pattern. In our
-- running example, @r@ could be either 'List1RowF' or 'List2RowF', while
-- @v@ could be either 'List1' or 'List2', respectively.
--
-- The pattern for the \"fixed\" constructor fixes the @x@ parameter to
-- @OpenADT r@ (below).
--
-- @
-- pattern Nil :: (OpenAlg r "nilF" NilF (OpenADT r)) => OpenADT r
-- pattern Nil = 'Fix' NilF
-- @
--
-- Since the patterns for each constructor are fairly repetative with only the
-- name changing, "Data.OpenADT.TH" provides a function, 'mkVarPattern', that
-- generates these patterns for you! The function takes four parameters:
--
-- 1. the type of the constructor,
-- 2. the label to be used for the constructor in the row,
-- 3. the name of the \"fixed\" pattern,
-- 4. and the name of the base functor pattern.
--
--
-- For example, the constructors for 'Cons1F' and 'Cons2F' can be created with:
--
-- @
-- mkVarPattern ''Cons1F \"cons1F\" \"Cons1\" \"Cons1F\"
-- mkVarPattern ''Cons2F \"cons2F\" \"Cons2\" \"Cons2F\"
-- @

pattern NilF :: (OpenAlg r "nilF" NilF x) => VarF r x
pattern NilF <- VarF (view #nilF -> Just NilF')
  where NilF = VarF (IsJust #nilF NilF')

pattern Nil :: (OpenAlg r "nilF" NilF (OpenADT r)) => OpenADT r
pattern Nil = Fix NilF

mkVarPattern ''Cons1F "cons1F" "Cons1" "Cons1F"
mkVarPattern ''Cons2F "cons2F" "Cons2" "Cons2F"

-- * Constructing Values
--
-- $constructing
-- The patterns that we have written can be used to construct values as if they
-- were normal ADTs. The one caveat is that GHC cannot infer the types since
-- the variable @r@ in the patterns can be any row. This is, in practice, not
-- much of an issue as top-level type declarations are sufficient in most
-- cases.
--
-- For the remaining of this tutorial we will use the following lists in
-- examples:
--
-- @
-- exList1 :: List1 Int
-- exList1 = Cons1 0 (Cons1 1 Nil)
-- @
--
-- @
-- exList2 :: List2 Int
-- exList2 = Cons2 2 3 (Cons1 4 Nil)
-- @

-- | Construct a 'List1'. The patterns 'Cons1' and 'Nil' are used.
--
-- > >>> print exList1
-- > Fix (VarF (Cons1F' 0 (Fix (VarF (Cons1F' 1 (Fix (VarF NilF')))))))
exList1 :: List1 Int
exList1 = Cons1 0 (Cons1 1 Nil)

-- | Construct a 'List2'.
--
-- > >>> print exList2
-- > Fix (VarF (Cons2F' 2 3 (Fix (VarF (Cons1F' 4 (Fix (VarF NilF')))))))
exList2 :: List2 Int
exList2 = Cons2 2 3 (Cons1 4 Nil)

-- * Adding Constructors
--
-- $lifting
-- Adding constructors to an open ADT is easy. We can use 'cata' from the
-- recursion-schemes library to define a __cata__morphism (a bottom-up
-- traversal) over our ADT. At each node in our structure, we apply the
-- function 'diversifyF' (see also 'diversify'), which adds constructors to our
-- variant (without making any changes).
--
-- In the following example, a 'List1' is changed to a 'List2'. Note how the
-- type applications extension (-XTypeApplications) can be used to easily
-- specify the first type argument to 'diversifyF', which is the row the
-- variant is extended with.
--
-- @
-- result1 :: List2 Int
-- result1 = 'cata'
--   ('Fix' . 'diversifyF' @(\"cons2F\" .== Cons2F Int)) exList1
-- @

-- | The constructor 'Cons2F' is added to 'exList1' without changing its
-- structure.
--
-- > >>> print result1
-- > Fix (VarF (Cons1F' 0 (Fix (VarF (Cons1F' 1 (Fix (VarF NilF')))))))
result1 :: List2 Int
result1 = cata
  (Fix . diversifyF @("cons2F" .== Cons2F Int)) exList1

-- * Removing Constructors
--
-- $restricting
-- To convert an ADT of one type to another with /fewer/ constructors, we need
-- to specify how constructors are removed should they exist in the structure.
-- The function 'reduceVarF' removes the constructors in a structure
-- corresponding to the fields of the record ('Rec' from row-types) of its
-- first argument. This function may only be used to remove constructors; it
-- can not add or modify them. More specifically, it is constrained such that
-- the set of labels of the row of the input record must be exactly the set
-- of labels of the input 'VarF' /less/ the output 'VarF'. While more
-- constrained than strictly necessary, this allows GHC to infer types better.
-- Note in the example below that there are no annotations other than at the
-- top-level.
--
-- @
-- result2 :: List1 Int
-- result2 = 'cata' ('Fix' . 'reduceVarF' fns) exList2
--  where
--   fns = #cons2F .== \(Cons2F' a b x) -> Cons1F a (Cons1 b x)
-- @
--
-- In the following sections we will see how to manipulate open ADT structures
-- more generally.

-- | Remove a constructor using 'reduceVarF' to convert a 'List2' to a 'List1'.
--
-- > >>> print result2
-- > Fix (VarF (Cons1F' 2 (Fix (VarF (Cons1F' 3 (Fix (VarF (Cons1F' 4 (Fix (VarF NilF'))))))))))
result2 :: List1 Int
result2 = cata (Fix . reduceVarF fns) exList2
 where
  fns = #cons2F .== \(Cons2F' a b x) -> Cons1F a (Cons1 b x)

-- * Pattern Matching
--
-- $matching
-- We previously used our constructor patterns to create structures, but the
-- patterns are bidirectional, so we can just as easily match with them. For
-- example, we can write a standard recursion scheme.
--
-- @
-- result3 :: List2 Int
-- result3 = 'cata' alg exList1
--  where
--   alg :: Alg (List1F Int) (List2 Int)
--   alg (Cons1F a x) = Cons2 a a x
--   alg NilF = Nil
--   alg _ = error
--     "Unfortunately using these patterns will always result in non-\\
--     \\exhaustive pattern match errors, hence the default case. :("
-- @
--
-- Unfortunately, as noted in the default case of @alg@, GHC can not (does
-- not?) check the exhaustiveness of pattern synonyms. Using a default case
-- will get rid of non-exhaustiveness warnings, but could also hide bugs if it
-- is partial.

-- | Use \"traditional\" pattern matching to write an algebra over a 'List1'.
--
-- > >>> print result3
-- > Fix (VarF (Cons2F' 0 0 (Fix (VarF (Cons2F' 1 1 (Fix (VarF NilF')))))))
result3 :: List2 Int
result3 = cata alg exList1
 where
  alg :: Alg (List1F Int) (List2 Int)
  alg (Cons1F a x) = Cons2 a a x
  alg NilF = Nil
  alg _ = error $
    "Unfortunately using these patterns will always result in non-" <>
    "exhaustive pattern match errors, hence the default case. :("

-- * Explicit Cases
--
-- $cases
-- An alternative that does not produce incomplete pattern warnings is to use
-- the 'caseonF' or 'switchF' functions (which are versions of 'caseon' and
-- 'switch' that operate on a 'VarF'). Similar to 'reduceVarF', these functions
-- require a record of functions that are then applied to the variant. However,
-- 'caseonF' and 'switchF' are more general than 'reduceVarF' in the sense that
-- the return type of the functions are not restricted. Note that the labels
-- and functions of the provided record must exactly match that of the input
-- type: no constructors may be omitted, nor is it possible to write any kind
-- of default case.
--
-- @
-- result4 :: List1 String
-- result4 = 'cata' ('caseonF' r) exList1
--  where r = #nilF   .== (\NilF' -> Nil)
--         .+ #cons1F .== (\(Cons1F' a x) -> Cons1 (show @Int a) x)
-- @

-- | An alternative way of writing 'result3' using 'caseonF'.
--
-- > >>> print result4
-- > Fix (VarF (Cons2F' 0 0 (Fix (VarF (Cons2F' 1 1 (Fix (VarF NilF')))))))
result4 :: List2 Int
result4 = cata (caseonF r) exList1
 where r = #nilF   .== (\NilF' -> Nil)
        .+ #cons1F .== (\(Cons1F' a x) -> Cons2 a a x)

-- * A Type Class Approach
--
-- $classes
-- An alternative approach to direct pattern matching is using type classes to
-- define each case of an open ADT. The type class function can then be applied
-- to each value in an ADT recursively with 'cata' as we have seen before.
--
-- This approach is beneficial compared to direct pattern matching because the
-- compiler can find \"non-exhaustive matches\" in the form of missing
-- instances. Similar to patterns, the typeclasses are generic enough to work
-- on any open ADT type provided all of that type's constructors satisfy the
-- constraint.
--
-- Consider, for example, the following class that defines an operation for
-- modifying the contents of a list.
--
-- @
-- class OverList a a' r (f :: * -> *) where
--   fmapList' :: (a -> a') -> f (OpenADT r) -> OpenADT r
--
-- instance ( OpenAlg r "nilF" NilF (OpenADT r)) => OverList a a' r NilF where
--   fmapList' _ NilF' = Nil
--
-- instance ( OpenAlg r "cons1F" (Cons1F a') (OpenADT r)) => OverList a a' r (Cons1F a) where
--   fmapList' f (Cons1F' a x) = Cons1 (f a) x
--
-- instance ( OpenAlg r "cons2F" (Cons2F a') (OpenADT r)) => OverList a a' r (Cons2F a) where
--   fmapList' f (Cons2F' a b x) = Cons2 (f a) (f b) x
--
-- instance (Forall v (OverList a a' r)) => OverList a a' r (VarF v) where
--   fmapList' f = varFAlg @(OverList a a' r) (fmapList' f)
-- @
--
-- The class 'OverList' has instances for all the constructors of 'List1' and
-- 'List2'. The final step is to recursively apply 'fmapList'' to the ADT.
--
-- @
-- fmapList f = 'cata' (fmapList' f)
-- @
--
-- The function 'varFAlg' is used to apply 'fmapList'' to a 'VarF'. As long as
-- all constructors satisfy the required constraint ('OverList' in this case),
-- we do not need to know the exact constructor.
--
-- Note that the type of 'fmapList' is polymorphic in its input and output
-- rows. Using 'fmapList', we can operate on both 'List1' and 'List2' types, or
-- any type that combines the three constructors that have 'OverList'
-- instances.

-- | This type class defines a fmap-like operation over lists.
class OverList a a' r (f :: * -> *) where
  fmapList' :: (a -> a') -> f (OpenADT r) -> OpenADT r

instance ( OpenAlg r "nilF" NilF (OpenADT r)
         ) => OverList a a' r NilF where
  fmapList' _ NilF' = Nil

instance ( OpenAlg r "cons1F" (Cons1F a') (OpenADT r)
         ) => OverList a a' r (Cons1F a) where
  fmapList' f (Cons1F' a x) = Cons1 (f a) x

instance ( OpenAlg r "cons2F" (Cons2F a') (OpenADT r)
         ) => OverList a a' r (Cons2F a) where
  fmapList' f (Cons2F' a b x) = Cons2 (f a) (f b) x

instance (Forall v (OverList a a' r)) => OverList a a' r (VarF v) where
  fmapList' f = varFAlg @(OverList a a' r) (fmapList' f)

-- | Apply the 'fmapList'' function to any @(OpenADT r)@ provided all its
-- constructors satisfy the constraint @(OverList a a' s)@.
fmapList :: forall a a' r s.
            ( Forall r Functor
            , Forall r (OverList a a' s)
            )
            => (a -> a') -> OpenADT r -> OpenADT s
fmapList f = cata (fmapList' f)

-- | Demonstrate that 'fmapList' can be applied to 'exList1'.
--
-- > result5 = fmapList (show @Int) exList1 :: List1 String
--
-- > >>> print result5
-- > Fix (VarF (Cons1F' "0" (Fix (VarF (Cons1F' "1" (Fix (VarF NilF')))))))
result5  :: List1 String
result5 = fmapList (show @Int) exList1

-- | Demonstrate that 'fmapList' can be applied to 'exList2'.
--
-- > result6 = fmapList (show @Int) exList2 :: List2 String
--
-- > >>> print result6
-- > Fix (VarF (Cons2F' "2" "3" (Fix (VarF (Cons1F' "4" (Fix (VarF NilF')))))))
result6  :: List2 String
result6 = fmapList (show @Int) exList2

-- * Combining Explicit Cases and Type Classes
--
-- $cases2
-- Suppose we have an ADT where we want to operate on a subset of its
-- constructors. For example, a subset of constructors do not implement a type
-- class that the others do, or perhaps we just want to override a single
-- constructor while using some default implementation for the other cases.
-- These situations can be handled with the type class approach just discussed
-- with overlappable instances. Unfortunately, among other issues, we do not
-- receive compiler errors if we add a constructor but forget to write its
-- instance; the default instance automatically takes over.
--
-- Fortunately, we can use a combination of explicit cases and the type class
-- approach to prevent this from happening. The idea is to partition the ADT
-- variant and handle each set of constructors separately. To partition the
-- ADT, we can use 'multiTrialF' (see also 'multiTrial') one or more times.
--
-- @
-- result7 = 'cata' alg exList2 where
--   alg :: Alg (List2F Int) (List1 String)
--   alg w = case 'multiTrialF' @("cons2F" .== Cons2F Int) w of
--
--     -- Explicit handling of specified constructors
--     Left v -> 'caseonF' r v
--
--     -- All others handled by fmapList'
--     Right leftovers -> 'fmapList'' (show @Int) leftovers
--
--   r = #cons2F .== \(Cons2F' a b x) ->
--         Cons1 ("(" <> show a <> " : " <> show b <> ")") x
-- @

-- | Demonstrate how to handle subsets of a 'VarF' individually.
--
-- Below is an alternate, but identical, implementation for the case where one
-- subset of variants matched is a single variant ('trialF' is used instead of
-- 'multiTrialF').
--
-- @
-- result7 = 'cata' alg exList2 where
--   alg w = case 'trialF' w #cons2F of
--     Left (Cons2F' a b x) -> Cons1 ("(" <> show a <> " : " <> show b <> ")") x
--     Right leftovers -> 'fmapList'' (show @Int) leftovers
-- @
--
-- > >>> print result7
-- > Fix (VarF (Cons1F' "(2 : 3)" (Fix (VarF (Cons1F' "4" (Fix (VarF NilF')))))))
result7 :: List1 String
result7 = cata alg exList2 where
  alg :: Alg (List2F Int) (List1 String)
  alg w = case multiTrialF @("cons2F" .== Cons2F Int) w of

    -- Explicit handling of specified constructors
    Left v -> caseonF r v

    -- All others handled by fmapList'
    Right leftovers -> fmapList' (show @Int) leftovers

  r = #cons2F .== \(Cons2F' a b x) ->
        Cons1 ("(" <> show a <> " : " <> show b <> ")") x

-- | This is the function invoked by the executable in this package. It simply
-- prints out the examples.
main' :: IO ()
main' = do
  putStrLn "exList1:"
  print exList1

  putStrLn "\nexList2:"
  print exList2

  putStrLn "\nresult1:"
  print result1

  putStrLn "\nresult2:"
  print result2

  putStrLn "\nresult3:"
  print result3

  putStrLn "\nresult4:"
  print result4

  putStrLn "\nresult5:"
  print result5

  putStrLn "\nresult6:"
  print result6

  putStrLn "\nresult7:"
  print result7
