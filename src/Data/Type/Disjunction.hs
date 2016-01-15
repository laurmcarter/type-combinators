{-# LANGUAGE StandaloneDeriving #-}
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
-- Module      :  Data.Type.Disjunction
-- Copyright   :  Copyright (C) 2015 Kyle Carter
-- License     :  BSD3
--
-- Maintainer  :  Kyle Carter <kylcarte@indiana.edu>
-- Stability   :  experimental
-- Portability :  RankNTypes
--
-- Two type combinators for working with disjunctions:
-- A /branch/ combinator '(:|:)', and a /choice/ combinator '(:+:)'.
--
-- These are analogous to '(|||)' and '(+++)' from 'Control.Arrow',
-- respectively.
--
-----------------------------------------------------------------------------

module Data.Type.Disjunction where

import Data.Type.Quantifier
import Type.Class.Higher
import Type.Class.Known
import Type.Class.Witness
import Type.Family.Either

-- (:|:) {{{

data ((f :: k -> *) :|: (g :: k -> *)) :: k -> * where
  L :: !(f a) -> (f :|: g) a
  R :: !(g a) -> (f :|: g) a
infixr 4 :|:

deriving instance (Eq   (f a), Eq   (g a)) => Eq   ((f :|: g) a)
deriving instance (Ord  (f a), Ord  (g a)) => Ord  ((f :|: g) a)
deriving instance (Show (f a), Show (g a)) => Show ((f :|: g) a)
deriving instance (Read (f a), Read (g a)) => Read ((f :|: g) a)

instance (Eq1 f, Eq1 g) => Eq1 (f :|: g) where
  eq1 = \case
    L a -> \case
      L b -> a =#= b
      _   -> False
    R a -> \case
      R b -> a =#= b
      _   -> False

instance (Ord1 f, Ord1 g) => Ord1 (f :|: g) where
  compare1 = \case
    L a -> \case
      L b -> compare1 a b
      R _ -> LT
    R a -> \case
      L _ -> GT
      R b -> compare1 a b

instance (Show1 f, Show1 g) => Show1 (f :|: g) where
  showsPrec1 d = showParen (d > 10) . \case
    L a -> showString "L "
         . showsPrec1 11 a
    R b -> showString "R "
         . showsPrec1 11 b

instance (Read1 f, Read1 g) => Read1 (f :|: g) where
  readsPrec1 d = readParen (d > 10) $ \s0 ->
    [ (a >>- Some . L,s2)
    | ("L",s1) <- lex s0
    , (a,s2)   <- readsPrec1 11 s1
    ] ++
    [ (a >>- Some . R,s2)
    | ("R",s1) <- lex s0
    , (a,s2)   <- readsPrec1 11 s1
    ]

(>|<) :: (f a -> r) -> (g a -> r) -> (f :|: g) a -> r
f >|< g = \case
  L a -> f a
  R b -> g b
infixr 2 >|<

instance Functor1 ((:|:) f) where
  map1 f = \case
    L a -> L a
    R b -> R $ f b

instance Foldable1 ((:|:) f) where
  foldMap1 f = \case
    L _ -> mempty
    R b -> f b

instance Traversable1 ((:|:) f) where
  traverse1 f = \case
    L a -> pure $ L a
    R b -> R <$> f b

instance Bifunctor1 (:|:) where
  bimap1 f g = \case
    L a -> L $ f a
    R b -> R $ g b

instance (Witness p q (f a), Witness p q (g a)) => Witness p q ((f :|: g) a) where
  type WitnessC p q ((f :|: g) a) = (Witness p q (f a), Witness p q (g a))
  (\\) r = \case
    L a -> r \\ a
    R b -> r \\ b

-- }}}

-- (:+:) {{{

data ((f :: k -> *) :+: (g :: l -> *)) :: Either k l -> * where
  L' :: !(f a) -> (f :+: g) (Left  a)
  R' :: !(g b) -> (f :+: g) (Right b)
infixr 4 :+:

deriving instance (Eq   (f (FromLeft e)), Eq   (g (FromRight e))) => Eq   ((f :+: g) e)
deriving instance (Ord  (f (FromLeft e)), Ord  (g (FromRight e))) => Ord  ((f :+: g) e)
deriving instance (Show (f (FromLeft e)), Show (g (FromRight e))) => Show ((f :+: g) e)

instance (Eq1 f, Eq1 g) => Eq1 (f :+: g) where
  eq1 = \case
    L' a -> \case
      L' b -> a =#= b
      _    -> False
    R' a -> \case
      R' b -> a =#= b
      _    -> False

instance (Ord1 f, Ord1 g) => Ord1 (f :+: g) where
  compare1 = \case
    L' a -> \case
      L' b -> compare1 a b
      _    -> LT
    R' a -> \case
      R' b -> compare1 a b
      _    -> GT

instance (Show1 f, Show1 g) => Show1 (f :+: g) where
  showsPrec1 d = showParen (d > 10) . \case
    L' a -> showString "L' "
          . showsPrec1 11 a
    R' b -> showString "R' "
          . showsPrec1 11 b

instance (Read1 f, Read1 g) => Read1 (f :+: g) where
  readsPrec1 d = readParen (d > 10) $ \s0 ->
    [ (a >>- Some . L',s2)
    | ("L'",s1) <- lex s0
    , (a,s2)    <- readsPrec1 11 s1
    ] ++
    [ (a >>- Some . R',s2)
    | ("R'",s1) <- lex s0
    , (a,s2)    <- readsPrec1 11 s1
    ]

{-
instance (DecEquality f, DecEquality g) => DecEquality (f :+: g) where
  decideEquality = \case
    L' a -> \case
      L' b -> decCase (decideEquality a b) (\Refl -> Proven Refl) (\contra -> Refuted $ contra . toEquality fromLeftCong)
      R' _ -> Refuted $
    R' a -> \case
      L' b -> Refuted undefined
      R' b -> undefined
-}


(>+<) :: (forall a. (e ~ Left a) => f a -> r) -> (forall b. (e ~ Right b) => g b -> r) -> (f :+: g) e -> r
f >+< g = \case
  L' a -> f a
  R' b -> g b
infixr 2 >+<

instance Known f a => Known (f :+: g) (Left a) where
  type KnownC (f :+: g) (Left a) = Known f a
  known = L' known

instance Known g b => Known (f :+: g) (Right b) where
  type KnownC (f :+: g) (Right b) = Known g b
  known = R' known

instance Functor1 ((:+:) f) where
  map1 f = \case
    L' a -> L' a
    R' b -> R' $ f b

instance Foldable1 ((:+:) f) where
  foldMap1 f = \case
    L' _ -> mempty
    R' b -> f b

instance Traversable1 ((:+:) f) where
  traverse1 f = \case
    L' a -> pure $ L' a
    R' b -> R' <$> f b

instance Bifunctor1 (:+:) where
  bimap1 f g = \case
    L' a -> L' $ f a
    R' b -> R' $ g b

instance Witness p q (f a) => Witness p q ((f :+: g) (Left a)) where
  type WitnessC p q ((f :+: g) (Left a)) = Witness p q (f a)
  r \\ L' a = r \\ a

instance Witness p q (g b) => Witness p q ((f :+: g) (Right b)) where
  type WitnessC p q ((f :+: g) (Right b)) = Witness p q (g b)
  r \\ R' b = r \\ b

-- }}}

