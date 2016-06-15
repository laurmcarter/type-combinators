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
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Type.Conjunction
-- Copyright   :  Copyright (C) 2015 Kyle Carter
-- License     :  BSD3
--
-- Maintainer  :  Kyle Carter <kylcarte@indiana.edu>
-- Stability   :  experimental
-- Portability :  RankNTypes
--
-- Two type combinators for working with conjunctions:
-- A /fanout/ combinator '(:&:)', and a /par/ combinator '(:*:)'.
--
-- These are analogous to '(&&&)' and '(***)' from 'Control.Arrow',
-- respectively.
--
-----------------------------------------------------------------------------

module Data.Type.Conjunction where

import Data.Type.Index.Trans
import Type.Class.Higher
import Type.Class.Known
import Type.Class.Witness
import Type.Family.Tuple

-- (:&:) {{{

data ((f :: k -> *) :&: (g :: k -> *)) :: k -> * where
  (:&:) :: !(f a) -> !(g a) -> (f :&: g) a
infixr 6 :&:

deriving instance (Eq   (f a), Eq   (g a)) => Eq   ((f :&: g) a)
deriving instance (Ord  (f a), Ord  (g a)) => Ord  ((f :&: g) a)
deriving instance (Show (f a), Show (g a)) => Show ((f :&: g) a)
deriving instance (Read (f a), Read (g a)) => Read ((f :&: g) a)

instance (Eq1 f, Eq1 g) => Eq1 (f :&: g) where
  eq1 (a :&: b) (c :&: d) = a =#= c && b =#= d

instance (Ord1 f, Ord1 g) => Ord1 (f :&: g) where
  compare1 (a :&: b) (c :&: d) = compare1 a c `mappend` compare1 b d

instance (Show1 f, Show1 g) => Show1 (f :&: g) where
  showsPrec1 d (a :&: b) = showParen (d > 5)
    $ showsPrec1 11 a
    . showString " :&: "
    . showsPrec1 11 b

fanFst :: (f :&: g) a -> f a
fanFst (a :&: _) = a

fanSnd :: (f :&: g) a -> g a
fanSnd (_ :&: b) = b

(.&.) :: (f a -> h b) -> (g a -> i b) -> (f :&: g) a -> (h :&: i) b
(f .&. g) (a :&: b) = f a :&: g b
infixr 3 .&.

fanFirst :: (f a -> g a) -> (f :&: h) a -> (g :&: h) a
fanFirst f (a :&: b) = f a :&: b

uncurryFan :: (f a -> g a -> r) -> (f :&: g) a -> r
uncurryFan f (a :&: b) = f a b

curryFan :: ((f :&: g) a -> r) -> f a -> g a -> r
curryFan f a b = f (a :&: b)

instance (Known f a, Known g a) => Known (f :&: g) a where
  known = known :&: known

instance Functor1 ((:&:) f) where
  map1 f (a :&: b) = a :&: f b

instance Foldable1 ((:&:) f) where
  foldMap1 f (_ :&: b) = f b

instance Traversable1 ((:&:) f) where
  traverse1 f (a :&: b) = (:&:) a <$> f b

instance Bifunctor1 (:&:) where
  bimap1 f g (a :&: b) = f a :&: g b

instance (Witness p q (f a), Witness s t (g a)) => Witness (p,s) (q,t) ((f :&: g) a) where
  type WitnessC (p,s) (q,t) ((f :&: g) a) = (Witness p q (f a), Witness s t (g a))
  r \\ a :&: b = r \\ a \\ b

-- }}}

-- (:*:) {{{

data ((f :: k -> *) :*: (g :: l -> *)) :: (k,l) -> * where
  (:*:) :: !(f a) -> !(g b) -> (f :*: g) (a#b)
infixr 6 :*:

deriving instance (Eq   (f (Fst p)), Eq   (g (Snd p))) => Eq   ((f :*: g) p)
deriving instance (Ord  (f (Fst p)), Ord  (g (Snd p))) => Ord  ((f :*: g) p)
deriving instance (Show (f (Fst p)), Show (g (Snd p))) => Show ((f :*: g) p)
deriving instance (p ~ (a#b), Read (f a), Read (g b)) => Read ((f :*: g) p)

instance (Eq1 f, Eq1 g) => Eq1 (f :*: g) where
  eq1 (a :*: b) (c :*: d) = a =#= c && b =#= d

instance (Ord1 f, Ord1 g) => Ord1 (f :*: g) where
  compare1 (a :*: b) (c :*: d) = compare1 a c `mappend` compare1 b d

instance (Show1 f, Show1 g) => Show1 (f :*: g) where
  showsPrec1 d (a :*: b) = showParen (d > 5)
    $ showsPrec1 11 a
    . showString " :*: "
    . showsPrec1 11 b

parFst :: (f :*: g) p -> f (Fst p)
parFst (a :*: _) = a

parSnd :: (f :*: g) p -> g (Snd p)
parSnd (_ :*: b) = b

uncurryPar :: (forall a b. (p ~ (a#b)) => f a -> g b -> r) -> (f :*: g) p -> r
uncurryPar f (a :*: b) = f a b

curryPar :: ((f :*: g) (a#b) -> r) -> f a -> g b -> r
curryPar f a b = f (a :*: b)

instance (p ~ (a#b), Known f a, Known g b) => Known (f :*: g) p where
  known = known :*: known

instance Functor1 ((:*:) f) where
  map1 f (a :*: b) = a :*: f b

instance Foldable1 ((:*:) f) where
  foldMap1 f (_ :*: b) = f b

instance Traversable1 ((:*:) f) where
  traverse1 f (a :*: b) = (:*:) a <$> f b

instance Bifunctor1 (:*:) where
  bimap1 f g (a :*: b) = f a :*: g b

instance IxFunctor1 (IxSecond (:~:)) ((:*:) f) where
  imap1 f (a :*: b) = a :*: f (IxSecond Refl) b

-- f :: (k -> *) ==> ((:*:) f) :: (l -> *) -> (k,l) -> *

_fst :: (a#b) :~: (c#d) -> a :~: c
_fst Refl = Refl

_snd :: (a#b) :~: (c#d) -> b :~: d
_snd Refl = Refl

{-
instance (BoolEquality f, BoolEquality g) => BoolEquality (f :*: g) where
  (a :*: b) .== (c :*: d) = a .== c .&& b .== d
-}

instance (DecEquality f, DecEquality g) => DecEquality (f :*: g) where
  decideEquality (a :*: b) (c :*: d) = case decideEquality a c of
    Proven    p -> case decideEquality b d of
      Proven  q -> Proven  $ Refl \\ p \\ q
      Refuted q -> Refuted $ q . _snd
    Refuted   p -> Refuted $ p . _fst

instance (Witness p q (f a), Witness s t (g b), x ~ (a#b)) => Witness (p,s) (q,t) ((f :*: g) x) where
  type WitnessC (p,s) (q,t) ((f :*: g) x) = (Witness p q (f (Fst x)), Witness s t (g (Snd x)))
  r \\ a :*: b = r \\ a \\ b

-- }}}

-- (:&&:) {{{

data (f :: k -> *) :&&: (g :: k -> *) where
  (:&&:) :: !(f a) -> !(g a) -> f :&&: g
infixr 6 :&&:

instance (TestEquality f, TestEquality g, Eq1 f, Eq1 g) => Eq (f :&&: g) where
  p == q = case conjEq p q of
    Just (a :&&: b, c :&&: d) -> eq1 a b && eq1 c d
    _                         -> False

instance (Show1 f, Show1 g) => Show (f :&&: g) where
  showsPrec d (a :&&: b) = showParen (d > 6)
    $ showsPrec1 7 a
    . showString " :&&: "
    . showsPrec1 6 b

conjEq :: (TestEquality f, TestEquality g) => f :&&: g -> f :&&: g -> Maybe (f :&&: f, g :&&: g)
conjEq (a :&&: c) (b :&&: d) = a =?= b //? c =?= d //? return (a :&&: b,c :&&: d)

-- }}}

