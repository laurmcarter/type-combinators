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
import Data.Type.Sum.Left
import Data.Type.MQueue
import Type.Class.Witness
import Type.Family.List

data Eff r a
  = Ret a
  | forall b. E (FSum r b) (Arrs r b a)

type Arr  r a b = a -> Eff r b
type Arrs r     = MQueue (Eff r)

qApp :: Arrs r a b -> a -> Eff r b
qApp q x = case viewl q of
  V1 k -> k x
  k :>=> t -> case k x of
    Ret y -> qApp t y
    E u r -> E u $ r >< t

qComp :: (Eff r b -> Eff s c) -> Arrs r a b -> a -> Eff s c
qComp h g = h . qApp g

instance Functor (Eff r) where
  fmap f = \case
    Ret x -> Ret $ f x
    E u q -> E u $ q |> Ret . f

instance Applicative (Eff r) where
  pure = Ret
  (<*>) = \case
    Ret f -> \case
      Ret a -> Ret $ f a
      E u q -> E u $ q |> Ret . f
    E u q -> E u . (q |>) . \case
      Ret a -> Ret . ($ a)
      m     -> (<$> m)

instance Monad (Eff r) where
  m >>= k = case m of
    Ret a -> k a
    E u q -> E u $ q |> k

send :: (t ∈ r) => t v -> Eff r v
send = retSum . finj

run :: Eff Ø w -> w
run = \case
  Ret a -> a
  E x _ -> absurd $ nilFSum x

bind :: FSum r a -> (a -> Eff r b) -> Eff r b
bind v = E v . tsingleton

retSum :: FSum r a -> Eff r a
retSum = (`bind` Ret)

handle :: (a -> Eff r w)
  -> (forall v. t v -> (v -> Eff r w) -> Eff r w)
  -> Eff (t :< r) a -> Eff r w
handle ret h = go
  where
  go = \case
    Ret x -> ret x
    E u q -> either h bind (fdecomp u) $ qComp go q

act :: (t ∈ r) => (a -> Eff r w)
  -> (forall v. t v -> (v -> Eff r w) -> Eff r w)
  -> Eff r a -> Eff r w
act ret h = go
  where
  go = \case
    Ret x -> ret x
    E u q -> maybe (bind u) h (fprj u) $ qComp go q

