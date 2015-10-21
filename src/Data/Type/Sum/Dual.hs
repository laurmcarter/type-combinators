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
-- Module      :  Data.Type.Sum.Dual
-- Copyright   :  Copyright (C) 2015 Kyle Carter
-- License     :  BSD3
--
-- Maintainer  :  Kyle Carter <kylcarte@indiana.edu>
-- Stability   :  experimental
-- Portability :  RankNTypes
--
-- 'FSum' is a type combinators for representing disjoint sums of
-- many functors @(fs :: [k -> *])@ at a single index @(a :: k)@.
-- As opposed to one-functor-many-indices 'Sum'.
--
-----------------------------------------------------------------------------

module Data.Type.Sum.Dual where

import Data.Type.Index

import Type.Class.HFunctor
import Type.Class.Witness

import Type.Family.Constraint
import Type.Family.List

data FSum :: [k -> *] -> k -> * where
  FInL :: !(f a) -> FSum (f :< fs) a
  FInR :: !(FSum fs a) -> FSum (f :< fs) a

-- | There are no possible values of the type @FSum Ø a@.
nilSumF :: FSum Ø a -> Void
nilSumF = impossible

-- | Decompose a non-empty FSum into either its head or its tail.
decompF :: FSum (f :< fs) a -> Either (f a) (FSum fs a)
decompF = \case
  FInL a -> Left  a
  FInR s -> Right s

-- | Inject an element into an FSum.
injF :: (f ∈ fs) => f a -> FSum fs a
injF = injectFSum elemIndex

-- | Project an implicit index out of an FSum.
prjF :: (f ∈ fs) => FSum fs a -> Maybe (f a)
prjF = indexF elemIndex

-- | Inject an element into an FSum with an explicitly
--   specified Index.
injectFSum :: Index fs f -> f a -> FSum fs a
injectFSum = \case
  IZ   -> FInL
  IS x -> FInR . injectFSum x

-- | Project an explicit index out of an FSum.
indexF :: Index fs f -> FSum fs a -> Maybe (f a)
indexF = \case
  IZ -> \case
    FInL a -> Just a
    _      -> Nothing
  IS x -> \case
    FInR s -> indexF x s
    _      -> Nothing

instance ListC (Functor <$> fs) => Functor (FSum fs) where
  fmap f = \case
    FInL a -> FInL $ f <$> a
    FInR s -> FInR $ f <$> s

instance ListC (Foldable <$> fs) => Foldable (FSum fs) where
  foldMap f = \case
    FInL a -> foldMap f a
    FInR s -> foldMap f s

instance
  ( ListC (Functor     <$> fs)
  , ListC (Foldable    <$> fs)
  , ListC (Traversable <$> fs)
  ) => Traversable (FSum fs) where
  traverse f = \case
    FInL a -> FInL <$> traverse f a
    FInR s -> FInR <$> traverse f s

-- | Map over the single element in an FSum
--   with a function that can handle any possible
--   element, along with the element's index.
imapF :: (forall f. Index fs f -> f a -> f b)
  -> FSum fs a -> FSum fs b
imapF f = \case
  FInL a -> FInL $ f IZ a
  FInR s -> FInR $ imapF (f . IS) s

-- | Fun fact: Since there is exactly one element in
--   an FSum, we don't need the @Monoid@ instance!
ifoldMapF :: (forall f. Index fs f -> f a -> m)
  -> FSum fs a -> m
ifoldMapF f = \case
  FInL a -> f IZ a
  FInR s -> ifoldMapF (f . IS) s

-- | Another fun fact: Since there is exactly one element in
--   an FSum, we require only a @Functor@ instance on @g@, rather
--   than @Applicative@.
itraverseF :: Functor g
  => (forall f. Index fs f -> f a -> g (f b))
  -> FSum fs a -> g (FSum fs b)
itraverseF f = \case
  FInL a -> FInL <$> f IZ a
  FInR s -> FInR <$> itraverseF (f . IS) s

