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

module Data.Type.MQueue where

data MQueue m a b where
  Leaf :: (a -> m b) -> MQueue m a b
  Node :: MQueue m a x -> MQueue m x b -> MQueue m a b

tsingleton :: (a -> m b) -> MQueue m a b
tsingleton = Leaf
{-# INLINE tsingleton #-}

(|>) :: MQueue m a b -> (b -> m c) -> MQueue m a c
t |> k = Node t (Leaf k)
{-# INLINE (|>) #-}
infixl 1 |>

(><) :: MQueue m a b -> MQueue m b c -> MQueue m a c
(><) = Node
{-# INLINE (><) #-}
infixl 1 ><

data ViewL m a b where
  V1   :: (a -> m b) -> ViewL m a b
  (:|) :: (a -> m x) -> MQueue m x b -> ViewL m a b
infix 2 :|

viewl :: MQueue m a b -> ViewL m a b
viewl = \case
  Leaf k   -> V1 k
  Node l r -> go l r
  where
  go :: MQueue m a x -> MQueue m x b -> ViewL m a b
  go = \case
    Leaf k   -> (k :|)
    Node l r -> go l . Node r
{-# INLINE viewl #-}

