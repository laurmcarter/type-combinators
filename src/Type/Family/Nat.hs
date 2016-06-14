{-# LANGUAGE TypeFamilyDependencies #-}
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
-- Module      :  Type.Family.Nat
-- Copyright   :  Copyright (C) 2015 Kyle Carter
-- License     :  BSD3
--
-- Maintainer  :  Kyle Carter <kylcarte@indiana.edu>
-- Stability   :  experimental
-- Portability :  RankNTypes
--
-- Type-level natural numbers, along with frequently used
-- type families over them.
--
-----------------------------------------------------------------------------

module Type.Family.Nat where

import Data.Type.Equality
import Type.Family.Bool
import Type.Family.Constraint
import Type.Family.List
import Type.Class.Witness

data N
  = Z
  | S N
  deriving (Eq,Ord,Show)

fromInt :: Int -> Maybe N
fromInt n = case compare n 0 of
  LT -> Nothing
  EQ -> Just Z
  GT -> S <$> fromInt (n-1)

type family IsZero (x :: N) :: Bool where
  IsZero Z     = True
  IsZero (S x) = False

zeroCong :: (x ~ y) :- (IsZero x ~ IsZero y)
zeroCong = Sub Wit

zNotS :: (Z ~ S x) :- Fail
zNotS = zeroCong

type family NatEq (x :: N) (y :: N) :: Bool where
  NatEq  Z     Z    = True
  NatEq  Z    (S y) = False
  NatEq (S x)  Z    = False
  NatEq (S x) (S y) = NatEq x y
type instance x == y = NatEq x y

type family Iota (x :: N) = (xs :: [N]) | xs -> x where
  Iota Z     = Ø
  Iota (S x) = x :< Iota x

iotaCong :: (x ~ y) :- (Iota x ~ Iota y)
iotaCong = Sub Wit

type family Pred (x :: N) :: N where
  Pred (S n) = n

type Pos n = (n ~ S (Pred n))

predCong :: (x ~ y) :- (Pred x ~ Pred y)
predCong = Sub Wit

type family (x :: N) + (y :: N) :: N where
  Z   + y = y
  S x + y = S (x + y)
infixr 6 +

data AddW (f :: N -> *) :: N -> * where
  AddW :: !(f x)
       -> !(f y)
       -> AddW f (x + y)

addCong :: (w ~ y,x ~ z) :- ((w + x) ~ (y + z))
addCong = Sub Wit

type family (x :: N) * (y :: N) :: N where
  Z   * y = Z
  S x * y = (x * y) + y
infixr 7 *

data MulW (f :: N -> *) :: N -> * where
  MulW :: !(f x)
       -> !(f y)
       -> MulW f (x * y)

mulCong :: (w ~ y,x ~ z) :- ((w * x) ~ (y * z))
mulCong = Sub Wit

type family (x :: N) ^ (y :: N) :: N where
  x ^   Z = S Z
  x ^ S y = (x ^ y) * x
infixl 8 ^

expCong :: (w ~ y,x ~ z) :- ((w ^ x) ~ (y ^ z))
expCong = Sub Wit

type family Len (as :: [k]) :: N where
  Len  Ø        = Z
  Len (a :< as) = S (Len as)

lenCong :: (as ~ bs) :- (Len as ~ Len bs)
lenCong = Sub Wit

type family Ix (x :: N) (as :: [k]) :: k where
  Ix Z     (a :< as) = a
  Ix (S x) (a :< as) = Ix x as

ixCong :: (x ~ y,as ~ bs) :- (Ix x as ~ Ix y bs)
ixCong = Sub Wit

type family (x :: N) < (y :: N) :: Bool where
  Z   < Z   = False
  Z   < S y = True
  S x < Z   = False
  S x < S y = x < y
infix 4 <

type x <= y = (x == y) || (x < y)
infix 4 <=

type family (x :: N) > (y :: N) :: Bool where
  Z   > Z   = False
  Z   > S y = False
  S x > Z   = True
  S x > S y = x > y
infix 4 >

type x >= y = (x == y) || (x > y)
infix 4 >=

-- | Convenient aliases for low-value Peano numbers.
type N0  = Z
type N1  = S N0
type N2  = S N1
type N3  = S N2
type N4  = S N3
type N5  = S N4
type N6  = S N5
type N7  = S N6
type N8  = S N7
type N9  = S N8
type N10 = S N9

