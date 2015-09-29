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

import Data.Type.Nat
import Type.Family.Nat

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

weaken :: Fin n -> Fin (S n)
weaken = \case
  FZ   -> FZ
  FS n -> FS $ weaken n

class (x :: N) <= (y :: N) where
  weakenN :: Fin x -> Fin y

instance {-# OVERLAPPING #-} x <= x where
  weakenN = id

instance {-# OVERLAPPABLE #-} (x <= y) => x <= S y where
  weakenN = weaken . weakenN

