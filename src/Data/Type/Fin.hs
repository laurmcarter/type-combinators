{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
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

module Data.Type.Fin where

import Data.Type.Combinator
import Data.Type.Nat
import Type.Class.Known
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

fins :: Nat n -> [Fin n]
fins = \case
  Z_   -> []
  S_ x -> FZ : map FS (fins x)

fin :: Fin n -> Int
fin = \case
  FZ   -> 0
  FS x -> succ $ fin x

finZ :: Fin Z -> Void
finZ = impossible

weaken :: Fin n -> Fin (S n)
weaken = \case
  FZ   -> FZ
  FS n -> FS $ weaken n

without :: Fin n -> Fin n -> Maybe (Fin (Pred n))
without = \case
  FZ -> \case
    FZ   -> Nothing
    FS y -> Just y
  FS x -> \case
    FZ   -> Just FZ \\ x
    FS y -> FS <$> without x y \\ x

class (x :: N) <= (y :: N) where
  weakenN :: Fin x -> Fin y

instance {-# OVERLAPPING #-} x <= x where
  weakenN = id

instance {-# OVERLAPPABLE #-} (x <= y) => x <= S y where
  weakenN = weaken . weakenN

{-
instance Known Nat n => Known ([] :.: Fin) n where
  type KnownC ([] :.: Fin) n = Known Nat n
  known = Comp $ go (known :: Nat n)
    where
    go :: Nat x -> [Fin x]
    go = \case
      Z_   -> []
      S_ x -> FZ : map FS (go x)
-}

finNat :: Fin x -> Some Nat
finNat = \case
  FZ   -> Some Z_
  FS x -> withSome (Some . S_) $ finNat x

instance (n' ~ Pred n) => Witness ØC (S n' ~ n) (Fin n) where
  type WitnessC ØC (S n' ~ n) (Fin n) = (n' ~ Pred n)
  (\\) r = \case
    FZ   -> r
    FS _ -> r

