{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE LambdaCase #-}

module Data.Type.Nat.Inequality where

import Data.Type.Nat
import Type.Class.Known
import Type.Class.Witness
import Type.Family.Constraint
import Type.Family.Nat

data NatLT :: N -> N -> * where
  LTZ :: NatLT Z (S y)
  LTS :: !(NatLT x y)
      -> NatLT (S x) (S y)

data NatEQ :: N -> N -> * where
  EQZ :: NatEQ Z Z
  EQS :: !(NatEQ x y)
      -> NatEQ (S x) (S y)

data NatGT :: N -> N -> * where
  GTZ :: NatGT (S x) Z
  GTS :: !(NatGT x y)
      -> NatGT (S x) (S y)

instance (lt ~ (x < y), eq ~ (x == y), gt ~ (x > y), y' ~ Pred y) => Witness ØC (y ~ S y', Known Nat x, lt ~ True, eq ~ False, gt ~ False) (NatLT x y) where
  type WitnessC ØC (y ~ S y', Known Nat x, lt ~ True, eq ~ False, gt ~ False) (NatLT x y) = (lt ~ (x < y), eq ~ (x == y), gt ~ (x > y), y' ~ Pred y)
  (\\) r = \case
    LTZ   -> r
    LTS l -> r \\ l

instance (lt ~ (x < y), eq ~ (x == y), gt ~ (x > y)) => Witness ØC (x ~ y, Known Nat x, lt ~ False, eq ~ True, gt ~ False) (NatEQ x y) where
  type WitnessC ØC (x ~ y, Known Nat x, lt ~ False, eq ~ True, gt ~ False) (NatEQ x y) = (lt ~ (x < y), eq ~ (x == y), gt ~ (x > y))
  (\\) r = \case
    EQZ   -> r
    EQS l -> r \\ l

instance (lt ~ (x < y), eq ~ (x == y), gt ~ (x > y), x' ~ Pred x) => Witness ØC (x ~ S x', Known Nat y, lt ~ False, eq ~ False, gt ~ True) (NatGT x y) where
  type WitnessC ØC (x ~ S x', Known Nat y, lt ~ False, eq ~ False, gt ~ True) (NatGT x y) = (lt ~ (x < y), eq ~ (x == y), gt ~ (x > y), x' ~ Pred x)
  (\\) r = \case
    GTZ   -> r
    GTS l -> r \\ l

natCompare :: Nat x -> Nat y -> Either (NatLT x y) (Either (NatEQ x y) (NatGT x y))
natCompare = \case
  Z_   -> \case
    Z_   -> Right $ Left EQZ
    S_ _ -> Left LTZ
  S_ x -> \case
    Z_   -> Right $ Right GTZ
    S_ y -> case natCompare x y of
      Left         lt  -> Left          $ LTS lt
      Right (Left  eq) -> Right $ Left  $ EQS eq
      Right (Right gt) -> Right $ Right $ GTS gt

