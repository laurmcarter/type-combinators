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

module Data.Type.Sum where

import Data.Type.Index

import Type.Class.HFunctor
import Type.Class.Witness

import Type.Family.Constraint
import Type.Family.List

data Sum (f :: k -> *) :: [k] -> * where
  InL :: !(f a) -> Sum f (a :< as)
  InR :: !(Sum f as) -> Sum f (a :< as)

decomp :: Sum f (a :< as) -> Either (f a) (Sum f as)
decomp = \case
  InL a -> Left  a
  InR s -> Right s

injectSum :: Index as a -> f a -> Sum f as
injectSum = \case
  IZ   -> InL
  IS x -> InR . injectSum x

inj :: Elem as a => f a -> Sum f as
inj = injectSum elemIndex

prj :: Elem as a => Sum f as -> Maybe (f a)
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

data Sum' :: [k -> *] -> k -> * where
  InL' :: !(f a) -> Sum' (f :< fs) a
  InR' :: !(Sum' fs a) -> Sum' (f :< fs) a

instance ListC (Functor <$> fs) => Functor (Sum' fs) where
  fmap f = \case
    InL' a -> InL' $ f <$> a
    InR' s -> InR' $ f <$> s

decomp' :: Sum' (f :< fs) a -> Either (f a) (Sum' fs a)
decomp' = \case
  InL' a -> Left  a
  InR' s -> Right s

inj' :: Elem fs f => f a -> Sum' fs a
inj' = injectSum' elemIndex

prj' :: Elem fs f => Sum' fs a -> Maybe (f a)
prj' = index' elemIndex

injectSum' :: Index fs f -> f a -> Sum' fs a
injectSum' = \case
  IZ   -> InL'
  IS x -> InR' . injectSum' x

index' :: Index fs f -> Sum' fs a -> Maybe (f a)
index' = \case
  IZ -> \case
    InL' a -> Just a
    _      -> Nothing
  IS x -> \case
    InR' s -> index' x s
    _      -> Nothing

