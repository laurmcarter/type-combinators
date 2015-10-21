{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Type.Sum
-- Copyright   :  Copyright (C) 2015 Kyle Carter
-- License     :  BSD3
--
-- Maintainer  :  Kyle Carter <kylcarte@indiana.edu>
-- Stability   :  experimental
-- Portability :  RankNTypes
--
-- 'Sum' is a type combinators for representing disjoint sums of
-- indices @(as :: [k])@ of a single functor @(f :: k -> *).
-- Contrast to the many-functors-one-index 'FSum'
--
-----------------------------------------------------------------------------

module Data.Type.Sum where

import Data.Type.Index

import Type.Class.HFunctor
import Type.Class.Witness

import Type.Family.Constraint
import Type.Family.List

data Sum (f :: k -> *) :: [k] -> * where
  InL :: !(f a) -> Sum f (a :< as)
  InR :: !(Sum f as) -> Sum f (a :< as)

-- | There are no possible values of the type @Sum f Ø@.
nilSum :: Sum f Ø -> Void
nilSum = impossible

decomp :: Sum f (a :< as) -> Either (f a) (Sum f as)
decomp = \case
  InL a -> Left  a
  InR s -> Right s

injectSum :: Index as a -> f a -> Sum f as
injectSum = \case
  IZ   -> InL
  IS x -> InR . injectSum x

inj :: (a ∈ as) => f a -> Sum f as
inj = injectSum elemIndex

prj :: (a ∈ as) => Sum f as -> Maybe (f a)
prj = index elemIndex

index :: Index as a -> Sum f as -> Maybe (f a)
index = \case
  IZ -> \case
    InL a -> Just a
    _     -> Nothing
  IS x -> \case
    InR s -> index x s
    _     -> Nothing

-- instances {{{

instance HFunctor Sum where
  map' f = \case
    InL a -> InL $ f a
    InR s -> InR $ map' f s

instance HIxFunctor Index Sum where
  imap' f = \case
    InL a -> InL $ f IZ a
    InR s -> InR $ imap' (f . IS) s

instance HFoldable Sum where
  foldMap' f = \case
    InL a -> f a
    InR s -> foldMap' f s

instance HIxFoldable Index Sum where
  ifoldMap' f = \case
    InL a -> f IZ a
    InR s -> ifoldMap' (f . IS) s

instance HTraversable Sum where
  traverse' f = \case
    InL a -> InL <$> f a
    InR s -> InR <$> traverse' f s

instance HIxTraversable Index Sum where
  itraverse' f = \case
    InL a -> InL <$> f IZ a
    InR s -> InR <$> itraverse' (f . IS) s

instance Witness p q (f a) => Witness p q (Sum f '[a]) where
  type WitnessC p q (Sum f '[a]) = Witness p q (f a)
  (\\) r = \case
    InL a -> r \\ a
    _     -> error "impossible type"

instance (Witness p q (f a), Witness p q (Sum f (b :< as))) => Witness p q (Sum f (a :< b :< as)) where
  type WitnessC p q (Sum f (a :< b :< as)) = (Witness p q (f a), Witness p q (Sum f (b :< as)))
  (\\) r = \case
    InL a -> r \\ a
    InR s -> r \\ s

-- }}}

