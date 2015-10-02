{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
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

module Data.Type.Eff where

import Data.Type.Index
import Data.Type.Sum
import Data.Type.MQueue
import Type.Family.List

data Eff r a
  = Val a
  | forall b. E (SumF r b) (Arrs r b a)

type Arr  r a b = a -> Eff r b
type Arrs r     = MQueue (Eff r)

qApp :: Arrs r a b -> a -> Eff r b
qApp q x = case viewl q of
  V1 k -> k x
  k :| t -> case k x of
    Val y -> qApp t y
    E u q -> E u $ q >< t

qComp :: Arrs r a b -> (Eff r b -> Eff r' c) -> Arr r' a c
qComp g h = h . qApp g

instance Functor (Eff r) where
  fmap f = \case
    Val x -> Val $ f x
    E u q -> E u $ q |> Val . f

instance Applicative (Eff r) where
  pure = Val
  (<*>) = \case
    Val f -> \case
      Val a -> Val $ f a
      E u q -> E u $ q |> Val . f
    E u q -> \case
      Val a -> E u $ q |> Val . ($ a)
      m     -> E u $ q |> (<$> m)

instance Monad (Eff r) where
  m >>= k = case m of
    Val a -> k a
    E u q -> E u $ q |> k

send :: (t ∈ r) => t v -> Eff r v
send t = E (injF t) $ tsingleton Val

run :: Eff Ø w -> w
run = \case
  Val a -> a
  _     -> error "impossible type"

handleRelay :: (a -> Eff r w)
  -> (forall v. t v -> Arr r v w -> Eff r w)
  -> Eff (t :< r) a -> Eff r w
handleRelay ret h = loop
  where
  loop = \case
    Val x -> ret x
    E u q -> case decompF u of
      Left  x -> h x k
      Right u -> E u $ tsingleton k
      where
      k = qComp q loop

interpose :: (t ∈ r) => (a -> Eff r w)
  -> (forall v. t v -> Arr r v w -> Eff r w)
  -> Eff r a -> Eff r w
interpose ret h = loop
  where
  loop = \case
    Val x -> ret x
    E u q -> case prjF u of
      Just x -> h x k
      _      -> E u $ tsingleton k
      where
      k = qComp q loop

