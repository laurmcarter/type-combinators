{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RankNTypes #-}
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
-- Module      :  Type.Class.Higher
-- Copyright   :  Copyright (C) 2015 Kyle Carter
-- License     :  BSD3
--
-- Maintainer  :  Kyle Carter <kylcarte@indiana.edu>
-- Stability   :  experimental
-- Portability :  RankNTypes
--
-- Higher order analogs of type classes from the Prelude.
----------------------------------------------------------------------------

module Type.Class.Higher where

import Data.Type.Quantifier

-- EqN {{{

class Eq1 (f :: k -> *) where
  eq1 :: f a -> f a -> Bool
  default eq1 :: Eq (f a) => f a -> f a -> Bool
  eq1 = (==)
  neq1 :: f a -> f a -> Bool
  neq1 a b = not $ eq1 a b

(=#=) :: Eq1 f => f a -> f a -> Bool
(=#=) = eq1
infix 4 =#=

class Eq2 (f :: k -> l -> *) where
  eq2 :: f a b -> f a b -> Bool
  default eq2 :: Eq (f a b) => f a b -> f a b -> Bool
  eq2 = (==)
  neq2 :: f a b -> f a b -> Bool
  neq2 a b = not $ eq2 a b

(=##=) :: Eq2 f => f a b -> f a b -> Bool
(=##=) = eq2
infix 4 =##=

class Eq3 (f :: k -> l -> m -> *) where
  eq3 :: f a b c -> f a b c -> Bool
  default eq3 :: Eq (f a b c ) => f a b c -> f a b c -> Bool
  eq3 = (==)
  neq3 :: f a b c -> f a b c -> Bool
  neq3 a b = not $ eq3 a b

(=###=) :: Eq3 f => f a b c -> f a b c -> Bool
(=###=) = eq3
infix 4 =###=

-- }}}

-- OrdN {{{

class Eq1 f => Ord1 (f :: k -> *) where
  compare1 :: f a -> f a -> Ordering
  default compare1 :: Ord (f a) => f a -> f a -> Ordering
  compare1 = compare
  (<#) :: f a -> f a -> Bool
  a <# b = compare1 a b == LT
  (>#) :: f a -> f a -> Bool
  a ># b = compare1 a b == GT
  (<=#) :: f a -> f a -> Bool
  a <=# b = compare1 a b /= GT
  (>=#) :: f a -> f a -> Bool
  a >=# b = compare1 a b /= LT
infix 4 <#, >#, <=#, >=#

class Eq2 f => Ord2 (f :: k -> l -> *) where
  compare2 :: f a b -> f a b -> Ordering
  default compare2 :: Ord (f a b) => f a b -> f a b -> Ordering
  compare2 = compare
  (<##) :: f a b -> f a b -> Bool
  a <## b = compare2 a b == LT
  (>##) :: f a b -> f a b -> Bool
  a >## b = compare2 a b == GT
  (<=##) :: f a b -> f a b -> Bool
  a <=## b = compare2 a b /= GT
  (>=##) :: f a b -> f a b -> Bool
  a >=## b = compare2 a b /= LT
infix 4 <##, >##, <=##, >=##

class Eq3 f => Ord3 (f :: k -> l -> m -> *) where
  compare3 :: f a b c -> f a b c -> Ordering
  default compare3 :: Ord (f a b c) => f a b c -> f a b c -> Ordering
  compare3 = compare
  (<###) :: f a b c -> f a b c -> Bool
  a <### b = compare3 a b == LT
  (>###) :: f a b c -> f a b c -> Bool
  a >### b = compare3 a b == GT
  (<=###) :: f a b c -> f a b c -> Bool
  a <=### b = compare3 a b /= GT
  (>=###) :: f a b c -> f a b c -> Bool
  a >=### b = compare3 a b /= LT
infix 4 <###, >###, <=###, >=###

-- }}}

-- ShowN {{{

class Show1 (f :: k -> *) where
  showsPrec1 :: Int -> f a -> ShowS
  default showsPrec1 :: Show (f a) => Int -> f a -> ShowS
  showsPrec1 = showsPrec
  show1 :: f a -> String
  show1 = ($ "") . shows1

shows1 :: Show1 f => f a -> ShowS
shows1 = showsPrec1 0


class Show2 (f :: k -> l -> *) where
  showsPrec2 :: Int -> f a b -> ShowS
  default showsPrec2 :: Show (f a b) => Int -> f a b -> ShowS
  showsPrec2 = showsPrec
  show2 :: f a b -> String
  show2 = ($ "") . shows2

shows2 :: Show2 f => f a b -> ShowS
shows2 = showsPrec2 0


class Show3 (f :: k -> l -> m -> *) where
  showsPrec3 :: Int -> f a b c -> ShowS
  default showsPrec3 :: Show (f a b c) => Int -> f a b c -> ShowS
  showsPrec3 = showsPrec
  show3 :: f a b c -> String
  show3 = ($ "") . shows3

shows3 :: Show3 f => f a b c -> ShowS
shows3 = showsPrec3 0

-- }}}

-- ReadN {{{

class Read1 (f :: k -> *) where
  readsPrec1 :: Int -> ReadS (Some f)

reads1 :: Read1 f => ReadS (Some f)
reads1 = readsPrec1 0

readMaybe1 :: Read1 f => String -> Maybe (Some f)
readMaybe1 s = case reads1 s of
  [(f,"")] -> Just f
  _        -> Nothing


class Read2 (f :: k -> l -> *) where
  readsPrec2 :: Int -> ReadS (Some2 f)

reads2 :: Read2 f => ReadS (Some2 f)
reads2 = readsPrec2 0

readMaybe2 :: Read2 f => String -> Maybe (Some2 f)
readMaybe2 s = case reads2 s of
  [(f,"")] -> Just f
  _        -> Nothing


class Read3 (f :: k -> l -> m -> *) where
  readsPrec3 :: Int -> ReadS (Some3 f)

reads3 :: Read3 f => ReadS (Some3 f)
reads3 = readsPrec3 0

readMaybe3 :: Read3 f => String -> Maybe (Some3 f)
readMaybe3 s = case reads3 s of
  [(f,"")] -> Just f
  _        -> Nothing

-- }}}

-- FunctorN {{{

class Functor1 (t :: (k -> *) -> l -> *) where
  -- | Take a natural transformation to a lifted natural transformation.
  map1 :: (forall (a :: k). f a -> g a) -> t f b -> t g b

class IxFunctor1 (i :: l -> k -> *) (t :: (k -> *) -> l -> *) | t -> i where
  imap1 :: (forall (a :: k). i b a -> f a -> g a) -> t f b -> t g b

-- }}}

-- FoldableN {{{

class Foldable1 (t :: (k -> *) -> l -> *) where
  foldMap1 :: Monoid m => (forall (a :: k). f a -> m) -> t f b -> m

class IxFoldable1 (i :: l -> k -> *) (t :: (k -> *) -> l -> *) | t -> i where
  ifoldMap1 :: Monoid m => (forall (a :: k). i b a -> f a -> m) -> t f b -> m

-- }}}

-- TraversableN {{{

class (Functor1 t, Foldable1 t) => Traversable1 (t :: (k -> *) -> l -> *) where
  traverse1 :: Applicative h => (forall (a :: k). f a -> h (g a)) -> t f b -> h (t g b)

class (IxFunctor1 i t, IxFoldable1 i t) => IxTraversable1 (i :: l -> k -> *) (t :: (k -> *) -> l -> *) | t -> i where
  itraverse1 :: Applicative h => (forall (a :: k). i b a -> f a -> h (g a)) -> t f b -> h (t g b)

-- }}}

-- BifunctorN {{{

class Bifunctor1 (t :: (k -> *) -> (l -> *) -> m -> *) where
  bimap1 :: (forall (a :: k). f a -> h a)
         -> (forall (a :: l). g a -> i a)
         -> t f g b
         -> t h i b

class IxBifunctor1 (i :: m -> k -> *) (j :: m -> l -> *) (t :: (k -> *) -> (l -> *) -> m -> *) | t -> i j where
  ibimap1 :: (forall (a :: k). i b a -> f a -> f' a)
          -> (forall (a :: l). j b a -> g a -> g' a)
          -> t f  g  b
          -> t f' g' b

-- }}}

class HFunctor (t :: (k -> *) -> l -> *) where
  -- | Take a natural transformation to a lifted natural transformation.
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

class HIxBifunctor (i :: m -> k -> *) (j :: m -> l -> *) (t :: (k -> *) -> (l -> *) -> m -> *) | t -> i j where
  ibimap' :: (forall (a :: k). i b a -> f a -> f' a)
          -> (forall (a :: l). j b a -> g a -> g' a)
          -> t f  g  b
          -> t f' g' b

