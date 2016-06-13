{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
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
-- import Data.Type.Quantifier

import Type.Class.Higher
import Type.Class.Witness

import Type.Family.List

data Sum (f :: k -> *) :: [k] -> * where
  InL :: !(f a) -> Sum f (a :< as)
  InR :: !(Sum f as) -> Sum f (a :< as)

deriving instance ListC (Eq   <$> f <$> as) => Eq   (Sum f as)
deriving instance
  ( ListC (Eq   <$> f <$> as)
  , ListC (Ord  <$> f <$> as)
  ) => Ord  (Sum f as)
deriving instance ListC (Show <$> f <$> as) => Show (Sum f as)

instance Eq1 f => Eq1 (Sum f) where
  eq1 = \case
    InL a -> \case
      InL b -> a =#= b
      _     -> False
    InR a -> \case
      InR b -> a =#= b
      _     -> False

instance Ord1 f => Ord1 (Sum f) where
  compare1 = \case
    InL a -> \case
      InL b -> compare1 a b
      _     -> LT
    InR a -> \case
      InR b -> compare1 a b
      _     -> GT

instance Show1 f => Show1 (Sum f) where
  showsPrec1 d = showParen (d > 10) . \case
    InL a -> showString "InL "
           . showsPrec1 11 a
    InR b -> showString "InR "
           . showsPrec1 11 b

instance Read1 f => Read1 (Sum f) where
  readsPrec1 d = readParen (d > 10) $ \s0 ->
    [ (a >>- Some . InL,s2)
    | ("InL",s1) <- lex s0
    , (a,s2) <- readsPrec1 11 s1
    ] ++
    [ (a >>- Some . InR,s2)
    | ("InR",s1) <- lex s0
    , (a,s2) <- readsPrec1 11 s1
    ]

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

elimSum :: (forall x xs. f x -> p (x :< xs))
        -> (forall x xs. Index as x -> p xs -> p (x :< xs))
        -> Sum f as
        -> p as
elimSum t n = \case
  InL a -> t a
  InR s -> n IZ $ elimSum t (n . IS) s

-- instances {{{

instance Functor1 Sum where
  map1 f = \case
    InL a -> InL $ f a
    InR s -> InR $ map1 f s

instance IxFunctor1 Index Sum where
  imap1 f = \case
    InL a -> InL $ f IZ a
    InR s -> InR $ imap1 (f . IS) s

instance Foldable1 Sum where
  foldMap1 f = \case
    InL a -> f a
    InR s -> foldMap1 f s

instance IxFoldable1 Index Sum where
  ifoldMap1 f = \case
    InL a -> f IZ a
    InR s -> ifoldMap1 (f . IS) s

instance Traversable1 Sum where
  traverse1 f = \case
    InL a -> InL <$> f a
    InR s -> InR <$> traverse1 f s

instance IxTraversable1 Index Sum where
  itraverse1 f = \case
    InL a -> InL <$> f IZ a
    InR s -> InR <$> itraverse1 (f . IS) s

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

