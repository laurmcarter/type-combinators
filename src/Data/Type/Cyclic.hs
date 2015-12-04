{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
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
-- Module      :  Data.Type.Cyclic
-- Copyright   :  Copyright (C) 2015 Kyle Carter
-- License     :  BSD3
--
-- Maintainer  :  Kyle Carter <kylcarte@indiana.edu>
-- Stability   :  experimental
-- Portability :  RankNTypes
--
--
-----------------------------------------------------------------------------

module Data.Type.Cyclic where

import Data.Type.Index
import Data.Type.Product
import Type.Family.Constraint
import Type.Family.List
import Type.Class.HFunctor
import Data.Monoid

data T a
  = E
  | L a
  | P (T a)
  | B (T a) (T a)
  deriving (Eq,Ord,Show)

type Path = Prod Branch

data Branch :: Bool -> * where
  BrL :: Branch False
  BrR :: Branch True

class {-((a :=> p) ~ b) =>-} Pos (p :: [Bool]) (a :: T k) (b :: T k) | p a -> b where
  type PosC p a b :: Constraint
  type PosC p a b = ØC
  (.@) :: Cyclic as f a -> Path p -> Cyclic as f b
infixl 2 .@

{-
type family (:=>) (a :: T k) (p :: [Bool]) :: T k where
  L x   :=> Ø          = L x
  B a b :=> Ø          = B a b
  B a b :=> False :< p = a :=> p
  B a b :=> True  :< p = b :=> p
infixl 3 :=>
-}

instance (as ~ Ø) => Pos as (L x) (L x) where
  type PosC as (L x) (L x) = (as ~ Ø)
  c .@ _ = c
instance Pos Ø (B a b) (B a b) where
  c .@ _ = c
instance Pos as a c => Pos (False :< as) (B a b) c where
  type PosC (False :< as) (B a b) c = Pos as a c
  -- c .@ (BrL :< p) = case c of
  --   Node a b -> _
instance Pos as b c => Pos (True  :< as) (B a b) c where
  type PosC (True  :< as) (B a b) c = Pos as b c

data Cyclic (as :: [T k]) :: (k -> *) -> T k -> * where
  Leaf  :: !(f a)
        -> Cyclic as f (L a)
  (:@)  :: Pos p a b
        => !(Index as a)
        -> !(Path p)
        -> Cyclic as f (P b)
  Node  :: !(Cyclic (B E b :< as) f a)
        -> !(Cyclic (B a E :< as) f b)
        -> Cyclic as f (B a b)
infix 2 :@

brLeft :: Cyclic as f (B a b) -> Cyclic (B E b :< as) f a
brLeft (Node a _) = a

brRight :: Cyclic as f (B a b) -> Cyclic (B a E :< as) f b
brRight (Node _ b) = b

instance Indexed (Cyclic as f a) (Cyclic bs f a) as bs where
  mapIndex f = \case
    Leaf a   -> Leaf a
    x :@ p   -> f x :@ p
    Node a b -> Node (mapIndex (liftIndex f) a) (mapIndex (liftIndex f) b)

instance HFunctor (Cyclic as) where
  map' f = \case
    Leaf a   -> Leaf $ f a
    x :@ p   -> x :@ p
    Node a b -> Node (map' f a) (map' f b)

instance HFoldable (Cyclic as) where
  foldMap' f = \case
    Leaf a   -> f a
    (:@){}   -> mempty
    Node a b -> foldMap' f a <> foldMap' f b

instance HTraversable (Cyclic as) where
  traverse' f = \case
    Leaf a   -> Leaf <$> f a
    x :@ p   -> pure $ x :@ p
    Node a b -> Node <$> traverse' f a <*> traverse' f b

