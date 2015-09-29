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

module Data.Type.Product where

import Data.Type.Combinator ((:.:)(..),IT(..))
import Data.Type.Index
import Data.Type.Length
import Type.Class.HFunctor
import Type.Class.Known
import Type.Class.Witness
import Type.Family.Constraint
import Type.Family.List

data Prod (f :: k -> *) :: [k] -> * where
  Ø    :: Prod f Ø
  (:<) :: !(f a) -> !(Prod f as) -> Prod f (a :< as)
infixr 5 :<

pattern (:>) :: (f :: k -> *) (a :: k) -> f (b :: k) -> Prod f '[a,b]
pattern a :> b = a :< b :< Ø
infix 6 :>

only :: f a -> Prod f '[a]
only = (:< Ø)

head' :: Prod f (a :< as) -> f a
head' (a :< _) = a

tail' :: Prod f (a :< as) -> Prod f as
tail' (_ :< as) = as

(>:) :: Prod f as -> f a -> Prod f (as >: a)
(>:) = \case
  Ø       -> only
  b :< as -> (b :<) . (as >:)
infixl 6 >:

reverse' :: Prod f as -> Prod f (Reverse as)
reverse' = \case
  Ø       -> Ø
  a :< as -> reverse' as >: a

init' :: Prod f (a :< as) -> Prod f (Init' a as)
init' (a :< as) = case as of
  Ø      -> Ø
  (:<){} -> a :< init' as

last' :: Prod f (a :< as) -> f (Last' a as)
last' (a :< as) = case as of
  Ø      -> a
  (:<){} -> last' as

append' :: Prod f as -> Prod f bs -> Prod f (as ++ bs)
append' = \case
  Ø       -> id
  a :< as -> (a :<) . append' as

onHead' :: (f a -> f b) -> Prod f (a :< as) -> Prod f (b :< as)
onHead' f (a :< as) = f a :< as

onTail' :: (Prod f as -> Prod f bs) -> Prod f (a :< as) -> Prod f (a :< bs)
onTail' f (a :< as) = a :< f as

uncurry' :: (f a -> Prod f as -> r) -> Prod f (a :< as) -> r
uncurry' f (a :< as) = f a as

curry' :: (l ~ (a :< as)) => (Prod f l -> r) -> f a -> Prod f as -> r
curry' f a as = f $ a :< as

index :: Index as a -> Prod f as -> f a
index = \case
  IZ -> head'
  IS x -> index x . tail'

instance HFunctor Prod where
  map' f = \case
    Ø -> Ø
    a :< as -> f a :< map' f as

instance HIxFunctor Index Prod where
  imap' f = \case
    Ø -> Ø
    a :< as -> f IZ a :< imap' (f . IS) as

instance HFoldable Prod where
  foldMap' f = \case
    Ø       -> mempty
    a :< as -> f a `mappend` foldMap' f as

instance HIxFoldable Index Prod where
  ifoldMap' f = \case
    Ø       -> mempty
    a :< as -> f IZ a `mappend` ifoldMap' (f . IS) as

instance HTraversable Prod where
  traverse' f = \case
    Ø       -> pure Ø
    a :< as -> (:<) <$> f a <*> traverse' f as

instance Known (Prod f) Ø where
  known = Ø

instance (Known f a, Known (Prod f) as) => Known (Prod f) (a :< as) where
  type KnownC (Prod f) (a :< as) = (Known f a, Known (Prod f) as)
  known = known :< known

instance Witness ØC ØC (Prod f Ø) where
  r \\ _ = r

instance (Witness p q (f a), Witness s t (Prod f as)) => Witness (p,s) (q,t) (Prod f (a :< as)) where
  type WitnessC (p,s) (q,t) (Prod f (a :< as)) = (Witness p q (f a), Witness s t (Prod f as))
  r \\ (a :< as) = r \\ a \\ as

