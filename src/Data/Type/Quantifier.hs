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

import Data.Type.Combinator

data Some (f :: k -> *) :: * where
  Some :: f a -> Some f

-- | An eliminator for a 'Some' type.
--
-- NB: the result type of the eliminating function may
-- not refer to the universally quantified type index @a@.
--
-- This function deserves more documentation. It is a powerful
-- basis for working with correct-by-construction data.
-- It serves as an explicit delimiter in a program of where
-- the type index may be used and depended on, and where it may
-- not.
some :: Some f -> (forall a. f a -> r) -> r
some (Some a) f = f a

withSome :: (forall a. f a -> r) -> Some f -> r
withSome f (Some a) = f a

onSome :: (forall a. f a -> g b) -> Some f -> Some g
onSome f (Some a) = Some (f a)

type Some2 f = Some (Some :.: f)

pattern Some2 :: f a b -> Some2 f
pattern Some2 a = Some (Comp (Some a))

data All (f :: k -> *) :: * where
  All :: { instAll :: forall (a :: k). f a } -> All f

-- | A data type for natural transformations.
data (f :: k -> *) :-> (g :: k -> *) where
  NT :: (forall a. f a -> g a) -> f :-> g
infixr 4 :->

data (p :: k -> l -> *) :--> (q :: k -> l -> *) where
  NT2 :: (forall a b. p a b -> q a b) -> p :--> q
infixr 4 :-->

