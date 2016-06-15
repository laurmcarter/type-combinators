{-# LANGUAGE UndecidableSuperClasses #-}
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
-- Module      :  Data.Type.Fin.Indexed
-- Copyright   :  Copyright (C) 2015 Kyle Carter
-- License     :  BSD3
--
-- Maintainer  :  Kyle Carter <kylcarte@indiana.edu>
-- Stability   :  experimental
-- Portability :  RankNTypes
--
-- A @singleton@-esque type for representing members of finite sets,
-- indexed by its Nat value.
--
-----------------------------------------------------------------------------

module Data.Type.Fin.Indexed where

import Data.Type.Nat
import Type.Class.Higher
-- import Type.Class.Known
import Type.Class.Witness
import Type.Family.Constraint
import Type.Family.Nat
-- import Data.Type.Quantifier

data IFin :: N -> N -> * where
  IFZ :: IFin (S x) Z
  IFS :: !(IFin x y) -> IFin (S x) (S y)

deriving instance Eq   (IFin x y)
deriving instance Ord  (IFin x y)
deriving instance Show (IFin x y)

instance Eq1   (IFin x)
instance Ord1  (IFin x)
instance Show1 (IFin x)

instance Eq2   IFin
instance Ord2  IFin
instance Show2 IFin

instance Read2 IFin where
  readsPrec2 d = readParen (d > 10) $ \s0 ->
    [ (Some2 IFZ,s1)
    | ("IFZ",s1) <- lex s0
    ] ++ 
    [ (n >>-- Some2 . IFS,s2)
    | ("IFS",s1) <- lex s0
    , (n,s2)    <- readsPrec2 11 s1
    ]

class LTC x y => LessEq (x :: N) (y :: N) where
  type LTC x y :: Constraint
  liftIFin :: IFin x z -> IFin y z

instance LessEq Z y where
  type LTC Z y = ØC
  liftIFin = absurd . ifinZ

instance (y ~ S (Pred y), LessEq x (Pred y)) => LessEq (S x) y where
  type LTC (S x) y = (y ~ S (Pred y), LessEq x (Pred y))
  liftIFin = \case
    IFZ   -> IFZ
    IFS x -> IFS $ liftIFin x

ifinZ :: IFin Z x -> Void
ifinZ = impossible

weaken :: IFin x y -> IFin (S x) y
weaken = \case
  IFZ   -> IFZ
  IFS n -> IFS $ weaken n

ifinNat :: IFin x y -> Nat y
ifinNat = \case
  IFZ   -> Z_
  IFS n -> S_ $ ifinNat n

ifinVal :: IFin x y -> Int
ifinVal = natVal . ifinNat

onIFinPred :: (forall x. IFin m x -> IFin n x) -> IFin (S m) y -> IFin (S n) y
onIFinPred f = \case
  IFZ   -> IFZ
  IFS m -> IFS $ f m

{-
-- | Map a finite set to a lower finite set without
-- one of its members.
without :: IFin n x -> IFin n y -> Maybe (IFin (Pred n))
without = \case
  FZ -> \case
    FZ   -> Nothing
    FS y -> Just y
  FS x -> \case
    FZ   -> Just FZ \\ x
    FS y -> FS <$> without x y \\ x
-}

-- | An @IFin x y@ is a 'Witness' that @x >= 1@.
--
-- That is, @'Pred' x@ is well defined.
instance (x' ~ Pred x) => Witness ØC (S x' ~ x) (IFin x y) where
  type WitnessC ØC (S x' ~ x) (IFin x y) = (x' ~ Pred x)
  (\\) r = \case
    IFZ   -> r
    IFS _ -> r

{-
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
-}

