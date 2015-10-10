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
-- Module      :  Data.Type.Nat
-- Copyright   :  Copyright (C) 2015 Kyle Carter
-- License     :  BSD3
--
-- Maintainer  :  Kyle Carter <kylcarte@indiana.edu>
-- Stability   :  experimental
-- Portability :  RankNTypes
--
-- A @singleton@-esque type for representing Peano natural numbers.
--
-----------------------------------------------------------------------------

module Data.Type.Nat where

import Data.Type.Equality
import Data.Type.Product
import Type.Class.Known
import Type.Class.Witness
import Type.Family.Constraint
import Type.Family.List
import Type.Family.Nat

data Nat :: N -> * where
  Z_ :: Nat Z
  S_ :: !(Nat n) -> Nat (S n)

deriving instance Eq   (Nat n)
deriving instance Ord  (Nat n)
deriving instance Show (Nat n)

-- | @'Z_'@ is the canonical construction of a @'Nat' Z@.
instance Known Nat Z where
  known = Z_

-- | If @n@ is a canonical construction of @Nat n@,
-- @'S_' n@ is the canonical construction of @Nat (S n)@.
instance Known Nat n => Known Nat (S n) where
  type KnownC Nat (S n) = Known Nat n
  known = S_ known

-- | A @Nat n@ is a 'Witness' that there is a canonical
-- construction for @Nat n@.
instance Witness ØC (Known Nat n) (Nat n) where
  (\\) r = \case
    Z_   -> r
    S_ x -> r \\ x

instance TestEquality Nat where
  testEquality = \case
    Z_ -> \case
      Z_   -> Just Refl
      S_ _ -> Nothing
    S_ x -> \case
      Z_   -> Nothing
      S_ y -> testEquality x y /? qed

instance DecEquality Nat where
  decideEquality = \case
    Z_ -> \case
      Z_   -> Proven  _Z
      S_ _ -> Refuted _ZneS
    S_ x -> \case
      Z_   -> Refuted $ _ZneS . sym
      S_ y -> (_S <-> _s) <?> decideEquality x y

_Z :: Z :~: Z
_Z = Refl

_S :: x :~: y -> S x :~: S y
_S Refl = Refl

_s :: S x :~: S y -> x :~: y
_s Refl = Refl

_ZneS :: Z :~: S x -> Void
_ZneS = impossible

-- | A proof that 'Z' is also a right identity
-- for the addition of type-level 'Nat's.
addZ :: Nat x -> (x + Z) :~: x
addZ = \case
  Z_   -> Refl
  S_ x -> _S $ addZ x
{-# INLINE addZ #-}

addS :: Nat x -> Nat y -> S (x + y) :~: (x + S y)
addS = \case
  Z_   -> pure Refl
  S_ x -> _S . addS x
{-# INLINE addS #-}

(.+) :: Nat x -> Nat y -> Nat (x + y)
(.+) = \case
  Z_   -> id
  S_ x -> S_ . (x .+)
infixr 6 .+

(.*) :: Nat x -> Nat y -> Nat (x * y)
(.*) = \case
  Z_   -> const Z_
  S_ x -> (.+) <$> (x .*) <*> id
infixr 7 .*

(.^) :: Nat x -> Nat y -> Nat (x ^ y)
(.^) x = \case
  Z_   -> S_ Z_
  S_ y -> (x .^ y) .* x
infixl 8 .^

nat :: Nat n -> Int
nat = \case
  Z_   -> 0
  S_ x -> succ $ nat x

n0  :: Nat N0
n1  :: Nat N1
n2  :: Nat N2
n3  :: Nat N3
n4  :: Nat N4
n5  :: Nat N5
n6  :: Nat N6
n7  :: Nat N7
n8  :: Nat N8
n9  :: Nat N9
n10 :: Nat N10

n0  = Z_
n1  = S_ n0
n2  = S_ n1
n3  = S_ n2
n4  = S_ n3
n5  = S_ n4
n6  = S_ n5
n7  = S_ n6
n8  = S_ n7
n9  = S_ n8
n10 = S_ n9

