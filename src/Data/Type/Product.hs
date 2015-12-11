{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
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
-- Module      :  Data.Type.Product
-- Copyright   :  Copyright (C) 2015 Kyle Carter
-- License     :  BSD3
--
-- Maintainer  :  Kyle Carter <kylcarte@indiana.edu>
-- Stability   :  experimental
-- Portability :  RankNTypes
--
-- Type combinators for type-level lists,
-- lifting @(f :: k -> *)@ to @(Prod f :: [k] -> *)@,
-- as well as its constructions, manipulations, and
-- eliminations.
--
-- 'Prod' is similar in nature to a few others in the Haskell ecosystem, such as:
--
-- Oleg's 'HList', from <http://hackage.haskell.org/package/HList>, and
-- 
-- Kenneth Foner's 'ConicList', from <http://hackage.haskell.org/package/IndexedList-0.1.0.1/docs/Data-List-Indexed-Conic.html>.
--
-----------------------------------------------------------------------------

module Data.Type.Product where

import Data.Type.Combinator
import Data.Type.Conjunction
import Data.Type.Index
import Data.Type.Length
import Data.Type.Quantifier
import Type.Class.Higher
import Type.Class.Known
import Type.Class.Witness
import Type.Family.Constraint
import Type.Family.List

data Prod (f :: k -> *) :: [k] -> * where
  Ø    :: Prod f Ø
  (:<) :: !(f a) -> !(Prod f as) -> Prod f (a :< as)
infixr 5 :<

deriving instance ListC (Eq   <$> f <$> as) => Eq   (Prod f as)
deriving instance
  ( ListC (Eq   <$> f <$> as)
  , ListC (Ord  <$> f <$> as)
  ) => Ord  (Prod f as)
deriving instance ListC (Show <$> f <$> as) => Show (Prod f as)

instance TestEquality f => TestEquality (Prod f) where
  testEquality = \case
    Ø -> \case
      Ø -> qed
      _ -> Nothing
    a :< as -> \case
      b :< bs -> a =?= b //? as =?= bs //? qed
      _       -> Nothing

-- | Construct a two element Prod.
--   Since the precedence of (:>) is higher than (:<),
--   we can conveniently write lists like:
--
--   >>> a :< b :> c
--
--   Which is identical to:
--
--   >>> a :< b :< c :< Ø
--
pattern (:>) :: (f :: k -> *) (a :: k) -> f (b :: k) -> Prod f '[a,b]
pattern a :> b = a :< b :< Ø
infix 6 :>

-- | Build a singleton Prod.
only :: f a -> Prod f '[a]
only = (:< Ø)

-- | snoc function. insert an element at the end of the list.
(>:) :: Prod f as -> f a -> Prod f (as >: a)
(>:) = \case
  Ø       -> only
  b :< as -> (b :<) . (as >:)
infixl 6 >:

head' :: Prod f (a :< as) -> f a
head' (a :< _) = a

tail' :: Prod f (a :< as) -> Prod f as
tail' (_ :< as) = as

-- | Get all but the last element of a non-empty Prod.
init' :: Prod f (a :< as) -> Prod f (Init' a as)
init' (a :< as) = case as of
  Ø      -> Ø
  (:<){} -> a :< init' as

-- | Get the last element of a non-empty Prod.
last' :: Prod f (a :< as) -> f (Last' a as)
last' (a :< as) = case as of
  Ø      -> a
  (:<){} -> last' as

reverse' :: Prod f as -> Prod f (Reverse as)
reverse' = \case
  Ø       -> Ø
  a :< as -> reverse' as >: a

append' :: Prod f as -> Prod f bs -> Prod f (as ++ bs)
append' = \case
  Ø       -> id
  a :< as -> (a :<) . append' as

lookup' :: TestEquality f => f a -> Prod (f :&: g) as -> Maybe (g a)
lookup' a = \case
  Ø               -> Nothing
  (b :&: v) :< bs -> witMaybe (a =?= b) (Just v) $ lookup' a bs

lookupPar :: TestEquality f => f a -> Prod (f :*: g) as -> Maybe (Some g)
lookupPar a = \case
  Ø               -> Nothing
  (b :*: v) :< bs -> witMaybe (a =?= b) (Just $ Some v) $ lookupPar a bs

permute :: Known Length bs => (forall x. Index bs x -> Index as x) -> Prod f as -> Prod f bs
permute f as = permute' f as known

permute' :: (forall x. Index bs x -> Index as x) -> Prod f as -> Length bs -> Prod f bs
permute' f as = \case
  LZ   -> Ø
  LS l -> index (f IZ) as :< permute' (f . IS) as l

-- Tuple {{{

-- | A Prod of simple Haskell types.
type Tuple = Prod I

-- | Singleton Tuple.
only_ :: a -> Tuple '[a]
only_ = only . I

-- | Cons onto a Tuple.
pattern (::<) :: a -> Tuple as -> Tuple (a :< as)
pattern a ::< as = I a :< as
infixr 5 ::<

-- | Snoc onto a Tuple.
(>::) :: Tuple as -> a -> Tuple (as >: a)
(>::) = \case
  Ø       -> only_
  b :< as -> (b :<) . (as >::)
infixl 6 >::

-- }}}

elimProd :: p Ø -> (forall x xs. Index as x -> f x -> p xs -> p (x :< xs)) -> Prod f as -> p as
elimProd n c = \case
  Ø       -> n
  a :< as -> c IZ a $ elimProd n (c . IS) as

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

select :: Prod (Index as) bs -> Prod f as -> Prod f bs
select = \case
  Ø     -> pure Ø
  x:<xs -> (:<) <$> index x <*> select xs

instance Functor1 Prod where
  map1 f = \case
    Ø -> Ø
    a :< as -> f a :< map1 f as

instance IxFunctor1 Index Prod where
  imap1 f = \case
    Ø -> Ø
    a :< as -> f IZ a :< imap1 (f . IS) as

instance Foldable1 Prod where
  foldMap1 f = \case
    Ø       -> mempty
    a :< as -> f a `mappend` foldMap1 f as

instance IxFoldable1 Index Prod where
  ifoldMap1 f = \case
    Ø       -> mempty
    a :< as -> f IZ a `mappend` ifoldMap1 (f . IS) as

instance Traversable1 Prod where
  traverse1 f = \case
    Ø       -> pure Ø
    a :< as -> (:<) <$> f a <*> traverse1 f as

instance IxTraversable1 Index Prod where
  itraverse1 f = \case
    Ø       -> pure Ø
    a :< as -> (:<) <$> f IZ a <*> itraverse1 (f . IS) as

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

