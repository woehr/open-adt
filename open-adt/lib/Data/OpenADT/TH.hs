-- |
-- Module      : Data.OpenADT.TH
-- Copyright   : Copyright (c) Jordan Woehr, 2018
-- License     : BSD
-- Maintainer  : Jordan Woehr
-- Stability   : experimental
--
-- This module exports template haskell functions for generating tedious
-- boilerplate.

{-# Language PatternSynonyms #-}
{-# Language TemplateHaskell #-}
{-# Language ViewPatterns #-}

module Data.OpenADT.TH
  ( mkVarPattern
  )
where

import           Control.Monad                            ( replicateM )
import           Data.Functor.Foldable                    ( Fix(..) )
import           Data.List                                ( foldl'
                                                          , init
                                                          )

import           Language.Haskell.TH

import           Data.Row                                 ( Label(..) )
import           Data.Row.Variants                        ( pattern IsJust
                                                          , view
                                                          )
import           Data.OpenADT.VarF                        ( OpenAlg
                                                          , VarF(..)
                                                          )

-- | Create patterns for a variant constructor.
--
-- For example, for the type FooF with the constructor FooF':
--
-- > data FooF a x = FooF' a x
-- > $(mkVarPattern ''FooF "foo" "Foo" "FooF")
--
-- A pattern similar to the following will be generated:
--
-- > pattern FooF :: (OpenAlg r "foo" (FooF a) v) => a -> v -> VarF r v
-- > pattern FooF a v <- VarF (view (Label :: Label "foo") -> Just (FooF' a v))
-- >
-- > pattern Foo :: (OpenAlg r "foo" (FooF a) (OpenADT r))
-- >             => a -> OpenADT r -> OpenADT r
-- >   where FooF a v = VarF (IsJust (Label :: Label "foo") (FooF' a v))
-- > pattern Foo  a v = Fix (FooF a v)
mkVarPattern :: Name   -- ^ The 'Name' of the type to create patterns for.
             -> String -- ^ The label in the variant the constructor will have.
             -> String -- ^ The name of the fixed pattern.
             -> String -- ^ The name of the unfixed pattern.
             -> Q [Dec]
mkVarPattern tyName rowLabel pName pfName = do
  let patName   = mkName pName
  let patFName  = mkName pfName
  let rowLabelT = return $ LitT (StrTyLit rowLabel)

  TyConI dec <- reify tyName
  let (conBndrs, conArgTs, conName) = case dec of
        DataD _ _ tvs _ [NormalC n argTs] _ ->
          (tvs, fmap (return . snd) argTs, n)
        NewtypeD _ _ tvs _ (NormalC n argTs) _ ->
          (tvs, fmap (return . snd) argTs, n)
        _ -> error "Expected data declaration with one constructor or newtype"

  args <- replicateM (length conArgTs) (newName "a")

  let conTvs        = fmap bndrToVar conBndrs
  -- Init should not fail because the types should be functors, thus
  -- always have > 0 variables
  let appliedTyCon = return $ foldl' AppT (ConT tyName) (init conTvs)
  let argsP         = fmap VarP args
  let appliedConExp = return $ foldl' AppE (ConE conName) (fmap VarE args)
  let appliedPatF   = return $ ConP patFName (fmap VarP args)
  let appliedConPat = return $ ConP conName (fmap VarP args)

  r <- newName "r" -- row type variable
  let tvV         = return $ bndrToVar (last conBndrs) -- variant type variable
  let tvR         = varT r
  let adtR        = [t| Fix (VarF $tvR) |]

  let patBndrsF   = PlainTV r : conBndrs
  let patBndrs    = PlainTV r : init conBndrs
  let patTypeCtxF = [t| (OpenAlg $tvR $rowLabelT $appliedTyCon $tvV) |]
  let patTypeCtx  = [t| (OpenAlg $tvR $rowLabelT $appliedTyCon $adtR) |]
  let patRetTypeF = [t| VarF $tvR $tvV |]
  let patTypeTypeF = foldr funApp patRetTypeF conArgTs
  let patTypeType  = foldr (\x a -> do
          x' <- x
          v' <- tvV
          if x' == v' then funApp adtR a else funApp x a
        ) adtR conArgTs

  patTypeF <- forallT patBndrsF ((: []) <$> patTypeCtxF) patTypeTypeF
  patType  <- forallT patBndrs  ((: []) <$> patTypeCtx)  patTypeType

  patBody <-
    [p| VarF (view (Label :: Label $rowLabelT) -> Just $appliedConPat) |]

  patClause <- [| VarF (IsJust (Label :: Label $rowLabelT) $appliedConExp) |]

  fixedPatF <- [p| Fix $appliedPatF |]

  return
    [ PatSynSigD patFName patTypeF
    , PatSynD patFName
              (PrefixPatSyn args)
              (ExplBidir [Clause argsP (NormalB patClause) []])
              patBody
    , PatSynSigD patName patType
    , PatSynD patName (PrefixPatSyn args) ImplBidir fixedPatF
    ]

bndrName :: TyVarBndr -> Name
bndrName (PlainTV n   ) = n
bndrName (KindedTV n _) = n

bndrToVar :: TyVarBndr -> Type
bndrToVar = VarT . bndrName

-- a -> b -> (a -> b)
funApp :: Q Type -> Q Type -> Q Type
funApp a b = appT (appT arrowT a) b
