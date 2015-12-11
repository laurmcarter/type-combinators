{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
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
-- Module      :  Data.Type.Fin
-- Copyright   :  Copyright (C) 2015 Kyle Carter
-- License     :  BSD3
--
-- Maintainer  :  Kyle Carter <kylcarte@indiana.edu>
-- Stability   :  experimental
-- Portability :  RankNTypes
--
-- A @singleton@-esque type for representing members of finite sets.
--
-----------------------------------------------------------------------------

module Data.Type.Fin where

import Data.Type.Nat
import Type.Class.Witness
import Type.Family.Constraint
import Type.Family.Nat
import Data.Type.Quantifier

data Fin :: N -> * where
  FZ :: Fin (S n)
  FS :: !(Fin n) -> Fin (S n)

deriving instance Eq   (Fin n)
deriving instance Ord  (Fin n)
deriving instance Show (Fin n)

elimFin :: (forall x. p (S x))
        -> (forall x. Fin x -> p x -> p (S x))
        -> Fin n -> p n
elimFin z s = \case
  FZ   -> z
  FS n -> s n $ elimFin z s n

-- | Gives the list of all members of the finite set of size @n@.
fins :: Nat n -> [Fin n]
fins = \case
  Z_   -> []
  S_ x -> FZ : map FS (fins x)

fin :: Fin n -> Int
fin = \case
  FZ   -> 0
  FS x -> succ $ fin x

-- | There are no members of @Fin Z@.
finZ :: Fin Z -> Void
finZ = impossible

weaken :: Fin n -> Fin (S n)
weaken = \case
  FZ   -> FZ
  FS n -> FS $ weaken n

-- | Map a finite set to a lower finite set without
-- one of its members.
without :: Fin n -> Fin n -> Maybe (Fin (Pred n))
without = \case
  FZ -> \case
    FZ   -> Nothing
    FS y -> Just y
  FS x -> \case
    FZ   -> Just FZ \\ x
    FS y -> FS <$> without x y \\ x

-- | Take a 'Fin' to an existentially quantified 'Nat'.
finNat :: Fin x -> Some Nat
finNat = \case
  FZ   -> Some Z_
  FS x -> withSome (Some . S_) $ finNat x

-- | A @Fin n@ is a 'Witness' that @n >= 1@.
--
-- That is, @'Pred' n@ is well defined.
instance (n' ~ Pred n) => Witness ØC (S n' ~ n) (Fin n) where
  type WitnessC ØC (S n' ~ n) (Fin n) = (n' ~ Pred n)
  (\\) r = \case
    FZ   -> r
    FS _ -> r

