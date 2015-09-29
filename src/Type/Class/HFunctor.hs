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

module Type.Class.HFunctor where

class HFunctor (t :: (k -> *) -> l -> *) where
  map' :: (forall (a :: k). f a -> g a) -> t f b -> t g b

class HIxFunctor (i :: l -> k -> *) (t :: (k -> *) -> l -> *) | t -> i where
  imap' :: (forall (a :: k). i b a -> f a -> g a) -> t f b -> t g b

class HFoldable (t :: (k -> *) -> l -> *) where
  foldMap' :: Monoid m => (forall (a :: k). f a -> m) -> t f b -> m

class HIxFoldable (i :: l -> k -> *) (t :: (k -> *) -> l -> *) | t -> i where
  ifoldMap' :: Monoid m => (forall (a :: k). i b a -> f a -> m) -> t f b -> m

class (HFunctor t, HFoldable t) => HTraversable (t :: (k -> *) -> l -> *) where
  traverse' :: Applicative h => (forall (a :: k). f a -> h (g a)) -> t f b -> h (t g b)

class (HIxFunctor i t, HIxFoldable i t) => HIxTraversable (i :: l -> k -> *) (t :: (k -> *) -> l -> *) | t -> i where
  itraverse' :: Applicative h => (forall (a :: k). i b a -> f a -> h (g a)) -> t f b -> h (t g b)

class HBifunctor (t :: (k -> *) -> (l -> *) -> m -> *) where
  bimap' :: (forall (a :: k). f a -> h a)
         -> (forall (a :: l). g a -> i a)
         -> t f g b
         -> t h i b
