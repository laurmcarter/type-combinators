{-# LANGUAGE MultiParamTypeClasses #-}
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
-- Module      :  Data.Type.Option
-- Copyright   :  Copyright (C) 2015 Kyle Carter
-- License     :  BSD3
--
-- Maintainer  :  Kyle Carter <kylcarte@indiana.edu>
-- Stability   :  experimental
-- Portability :  RankNTypes
--
-- A type combinator for type-level @Maybe@s,
-- lifting @(f :: k -> *)@ to @(Option f :: Maybe k -> *)@.
--
-----------------------------------------------------------------------------

module Data.Type.Option where

import Type.Class.Higher
import Type.Class.Known
import Type.Class.Witness
import Type.Family.Maybe

data Option (f :: k -> *) :: Maybe k -> * where
  Nothing_ :: Option f Nothing
  Just_    :: !(f a) -> Option f (Just a)

-- | Eliminator for @'Option' f@.
option :: (forall a. (m ~ Just a) => f a -> r) -> ((m ~ Nothing) => r) -> Option f m -> r
option j n = \case
  Just_ a  -> j a
  Nothing_ -> n

-- | We can take a natural transformation of @(forall x. f x -> g x)@ to
-- a natural transformation of @(forall mx. 'Option' f mx -> 'Option' g mx)@.
instance Functor1 Option where
  map1 f = \case
    Just_ a  -> Just_ $ f a
    Nothing_ -> Nothing_

instance Foldable1 Option where
  foldMap1 f = \case
    Just_ a  -> f a
    Nothing_ -> mempty

instance Traversable1 Option where
  traverse1 f = \case
    Just_ a  -> Just_ <$> f a
    Nothing_ -> pure Nothing_

instance Known (Option f) Nothing where
  known = Nothing_

instance Known f a => Known (Option f) (Just a) where
  type KnownC (Option f) (Just a) = Known f a
  known = Just_ known

instance (Witness p q (f a), x ~ Just a) => Witness p q (Option f x) where
  type WitnessC p q (Option f x) = Witness p q (f (FromJust x))
  (\\) r = \case
    Just_ a -> r \\ a
    _       -> error "impossible type"

