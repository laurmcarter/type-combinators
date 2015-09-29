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

module Data.Type.Option where

import Type.Class.HFunctor
import Type.Class.Known
import Type.Class.Witness
import Type.Family.Maybe

data Option (f :: k -> *) :: Maybe k -> * where
  Nothing_ :: Option f Nothing
  Just_    :: !(f a) -> Option f (Just a)

option :: (forall a. (m ~ Just a) => f a -> r) -> ((m ~ Nothing) => r) -> Option f m -> r
option j n = \case
  Just_ a  -> j a
  Nothing_ -> n

instance HFunctor Option where
  map' f = \case
    Just_ a  -> Just_ $ f a
    Nothing_ -> Nothing_

instance HFoldable Option where
  foldMap' f = \case
    Just_ a  -> f a
    Nothing_ -> mempty

instance HTraversable Option where
  traverse' f = \case
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

