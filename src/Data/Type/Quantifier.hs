{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RankNTypes #-}
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
-- Module      :  Data.Type.Quantifier
-- Copyright   :  Copyright (C) 2015 Kyle Carter
-- License     :  BSD3
--
-- Maintainer  :  Kyle Carter <kylcarte@indiana.edu>
-- Stability   :  experimental
-- Portability :  RankNTypes
--
-- Types for working with (and under) existentially and universally
-- quantified types.
--
-- The 'Some' type can be very useful when working with type-indexed GADTs,
-- where defining instances for classes like 'Read' can be tedious at best,
-- and frequently impossible, for the GADT itself.
--
-----------------------------------------------------------------------------

module Data.Type.Quantifier where

import Type.Family.Constraint

-- Some {{{

data Some (f :: k -> *) :: * where
  Some :: f a -> Some f

-- | An eliminator for a 'Some' type.
--
-- Consider this function akin to a Monadic bind, except
-- instead of binding into a Monad with a sequent function,
-- we're binding into the existential quantification with
-- a universal eliminator function.
--
-- It serves as an explicit delimiter in a program of where
-- the type index may be used and depended on, and where it may
-- not.
--
-- NB: the result type of the eliminating function may
-- not refer to the universally quantified type index @a@.
--
some :: Some f -> (forall a. f a -> r) -> r
some (Some a) f = f a

(>>-) :: Some f -> (forall a. f a -> r) -> r
(>>-) = some
infixl 1 >>-

(>->) :: (forall x. f x -> Some g) -> (forall x. g x -> Some h) -> f a -> Some h
(f >-> g) a = f a >>- g
infixr 1 >->

withSome :: (forall a. f a -> r) -> Some f -> r
withSome f (Some a) = f a

onSome :: (forall a. f a -> g x) -> Some f -> Some g
onSome f (Some a) = Some (f a)

-- }}}

-- Some2 {{{

data Some2 (f :: k -> l -> *) :: * where
  Some2 :: f a b -> Some2 f

some2 :: Some2 f -> (forall a b. f a b -> r) -> r
some2 (Some2 a) f = f a

(>>--) :: Some2 f -> (forall a b. f a b -> r) -> r
(>>--) = some2
infixl 1 >>--

(>-->) :: (forall x y. f x y -> Some2 g) -> (forall x y. g x y -> Some2 h) -> f a b -> Some2 h
(f >--> g) a = f a >>-- g
infixr 1 >-->

withSome2 :: (forall a b. f a b -> r) -> Some2 f -> r
withSome2 f (Some2 a) = f a

onSome2 :: (forall a b. f a b -> g x y) -> Some2 f -> Some2 g
onSome2 f (Some2 a) = Some2 (f a)

-- }}}

-- Some3 {{{

data Some3 (f :: k -> l -> m -> *) :: * where
  Some3 :: f a b c -> Some3 f

some3 :: Some3 f -> (forall a b c. f a b c -> r) -> r
some3 (Some3 a) f = f a

(>>---) :: Some3 f -> (forall a b c. f a b c -> r) -> r
(>>---) = some3
infixl 1 >>---

(>--->) :: (forall x y z. f x y z -> Some3 g) -> (forall x y z. g x y z -> Some3 h) -> f a b c -> Some3 h
(f >---> g) a = f a >>--- g
infixr 1 >--->

withSome3 :: (forall a b c. f a b c -> r) -> Some3 f -> r
withSome3 f (Some3 a) = f a

onSome3 :: (forall a b c. f a b c -> g x y z) -> Some3 f -> Some3 g
onSome3 f (Some3 a) = Some3 (f a)

-- }}}

-- SomeC {{{

data SomeC (c :: k -> Constraint) (f :: k -> *) where
  SomeC :: c a => f a -> SomeC c f

someC :: SomeC c f -> (forall a. c a => f a -> r) -> r
someC (SomeC a) f = f a

(>>~) :: SomeC c f -> (forall a. c a => f a -> r) -> r
(>>~) = someC
infixl 1 >>~

-- }}}

-- EveryN {{{

data Every (f :: k -> *) :: * where
  Every :: { instEvery :: forall a. f a } -> Every f

data Every2 (f :: k -> l -> *) :: * where
  Every2 :: { instEvery2 :: forall a b. f a b } -> Every2 f

data Every3 (f :: k -> l -> m -> *) :: * where
  Every3 :: { instEvery3 :: forall a b c. f a b c } -> Every3 f

-- }}}

