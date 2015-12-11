{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RankNTypes #-}
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
-- Module      :  Data.Type.Product.Lifted
-- Copyright   :  Copyright (C) 2015 Kyle Carter
-- License     :  BSD3
--
-- Maintainer  :  Kyle Carter <kylcarte@indiana.edu>
-- Stability   :  experimental
-- Portability :  RankNTypes
--
-- Type combinators for type-level lists,
-- where we have many functors with a single index.
--
-----------------------------------------------------------------------------

module Data.Type.Product.Lifted where

import Data.Type.Index
import Type.Class.Known
import Type.Class.Witness
import Type.Family.Constraint
import Type.Family.List

import Data.Monoid ((<>))

data FProd (fs :: [k -> *]) :: k -> * where
  ØF   :: FProd Ø a
  (:<<) :: !(f a) -> !(FProd fs a) -> FProd (f :< fs) a
infixr 5 :<<

-- | Construct a two element FProd.
--   Since the precedence of (:>>) is higher than (:<<),
--   we can conveniently write lists like:
--
--   >>> a :<< b :>> c
--
--   Which is identical to:
--
--   >>> a :<< b :<< c :<< Ø
--
pattern (:>>) :: (f :: k -> *) (a :: k) -> (g :: k -> *) a -> FProd '[f,g] a
pattern a :>> b = a :<< b :<< ØF
infix 6 :>>

-- | Build a singleton FProd.
onlyF :: f a -> FProd '[f] a
onlyF = (:<< ØF)

-- | snoc function. insert an element at the end of the FProd.
(>>:) :: FProd fs a -> f a -> FProd (fs >: f) a
(>>:) = \case
  ØF       -> onlyF
  b :<< as -> (b :<<) . (as >>:)
infixl 6 >>:

headF :: FProd (f :< fs) a -> f a
headF (a :<< _) = a

tailF :: FProd (f :< fs) a -> FProd fs a
tailF (_ :<< as) = as

-- | Get all but the last element of a non-empty FProd.
initF :: FProd (f :< fs) a -> FProd (Init' f fs) a
initF (a :<< as) = case as of
  ØF     -> ØF
  (:<<){} -> a :<< initF as

-- | Get the last element of a non-empty FProd.
lastF :: FProd (f :< fs) a -> Last' f fs a
lastF (a :<< as) = case as of
  ØF      -> a
  (:<<){} -> lastF as

-- | Reverse the elements of an FProd.
reverseF :: FProd fs a -> FProd (Reverse fs) a
reverseF = \case
  ØF       -> ØF
  a :<< as -> reverseF as >>: a

-- | Append two FProds.
appendF :: FProd fs a -> FProd gs a -> FProd (fs ++ gs) a
appendF = \case
  ØF       -> id
  a :<< as -> (a :<<) . appendF as

-- | Map over the head of a non-empty FProd.
onHeadF :: (f a -> g a) -> FProd (f :< fs) a -> FProd (g :< fs) a
onHeadF f (a :<< as) = f a :<< as

-- | Map over the tail of a non-empty FProd.
onTailF :: (FProd fs a -> FProd gs a) -> FProd (f :< fs) a -> FProd (f :< gs) a
onTailF f (a :<< as) = a :<< f as

uncurryF :: (f a -> FProd fs a -> r) -> FProd (f :< fs) a -> r
uncurryF f (a :<< as) = f a as

curryF :: (l ~ (f :< fs)) => (FProd l a -> r) -> f a -> FProd fs a -> r
curryF f a as = f $ a :<< as

indexF :: Index fs f -> FProd fs a -> f a
indexF = \case
  IZ -> headF
  IS x -> indexF x . tailF

-- | If all @f@ in @fs@ are @Functor@s, then @FProd fs@ is a @Functor@.
instance ListC (Functor <$> fs) => Functor (FProd fs) where
  fmap f = \case
    ØF       -> ØF
    a :<< as -> fmap f a :<< fmap f as

-- | If all @f@ in @fs@ are @Foldable@s, then @FProd fs@ is a @Foldable@.
instance ListC (Foldable <$> fs) => Foldable (FProd fs) where
  foldMap f = \case
    ØF       -> mempty
    a :<< as -> foldMap f a <> foldMap f as

-- | If all @f@ in @fs@ are @Traversable@s, then @FProd fs@ is a @Traversable@.
instance
  ( ListC (Functor     <$> fs)
  , ListC (Foldable    <$> fs)
  , ListC (Traversable <$> fs)
  ) => Traversable (FProd fs) where
  traverse f = \case
    ØF       -> pure ØF
    a :<< as -> (:<<) <$> traverse f a <*> traverse f as

-- | Map over all elements of an FProd with access to the element's index.
imapF :: (forall f. Index fs f -> f a -> f b)
  -> FProd fs a -> FProd fs b
imapF f = \case
  ØF       -> ØF
  a :<< as -> f IZ a :<< imapF (f . IS) as

-- | Fold over all elements of an FProd with access to the element's index.
ifoldMapF :: Monoid m
  => (forall f. Index fs f -> f a -> m)
  -> FProd fs a -> m
ifoldMapF f = \case
  ØF       -> mempty
  a :<< as -> f IZ a <> ifoldMapF (f . IS) as

-- | Traverse over all elements of an FProd with access to the element's index.
itraverseF :: Applicative g
  => (forall f. Index fs f -> f a -> g (f b))
  -> FProd fs a -> g (FProd fs b)
itraverseF f = \case
  ØF       -> pure ØF
  a :<< as -> (:<<) <$> f IZ a <*> itraverseF (f . IS) as

instance Known (FProd Ø) a where
  known = ØF

instance (Known f a, Known (FProd fs) a) => Known (FProd (f :< fs)) a where
  type KnownC (FProd (f :< fs)) a = (Known f a, Known (FProd fs) a)
  known = known :<< known

-- | An empty FProd is a no-op Witness.
instance Witness ØC ØC (FProd Ø a) where
  r \\ _ = r

-- | A non-empty FProd is a Witness if both its head and tail are Witnesses.
instance (Witness p q (f a), Witness s t (FProd fs a)) => Witness (p,s) (q,t) (FProd (f :< fs) a) where
  type WitnessC (p,s) (q,t) (FProd (f :< fs) a) = (Witness p q (f a), Witness s t (FProd fs a))
  r \\ (a :<< as) = r \\ a \\ as

