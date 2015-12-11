{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DefaultSignatures #-}
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
-- Module      :  Data.Type.Combinator
-- Copyright   :  Copyright (C) 2015 Kyle Carter
-- License     :  BSD3
--
-- Maintainer  :  Kyle Carter <kylcarte@indiana.edu>
-- Stability   :  experimental
-- Portability :  RankNTypes
--
-- A collection of simple type combinators,
-- such as @Identity@ 'I', @Constant@ 'C', @Compose@ '(:.:)',
-- Currying/Uncurrying, etc.
--
-----------------------------------------------------------------------------

module Data.Type.Combinator where

import Type.Class.Known
import Type.Class.Witness
import Type.Family.Tuple

import Control.Applicative

-- (:.:) {{{

data ((f :: l -> *) :.: (g :: k -> l)) :: k -> * where
  Comp :: { getComp :: f (g a) } -> (f :.: g) a
infixr 6 :.:

deriving instance Eq   (f (g a)) => Eq   ((f :.: g) a)
deriving instance Ord  (f (g a)) => Ord  ((f :.: g) a)
deriving instance Show (f (g a)) => Show ((f :.: g) a)

instance Witness p q (f (g a)) => Witness p q ((f :.: g) a) where
  type WitnessC p q ((f :.: g) a) = Witness p q (f (g a))
  r \\ Comp a = r \\ a

instance TestEquality f => TestEquality (f :.: g) where
  testEquality (Comp a) (Comp b) = a =?= b //? qed

instance TestEquality f => TestEquality1 ((:.:) f) where
  testEquality1 (Comp a) (Comp b) = a =?= b //? qed

-- }}}

-- I {{{

data I :: * -> * where
  I :: { getI :: a } -> I a

deriving instance Eq   a => Eq   (I a)
deriving instance Ord  a => Ord  (I a)
deriving instance Show a => Show (I a)

instance Functor I where
  fmap f (I a) = I $ f a

instance Applicative I where
  pure = I
  I f <*> I a = I $ f a

instance Monad I where
  I a >>= f = f a

instance Foldable I where
  foldMap f (I a) = f a

instance Traversable I where
  traverse f (I a) = I <$> f a

instance Witness p q a => Witness p q (I a) where
  type WitnessC p q (I a) = Witness p q a
  r \\ I a = r \\ a

instance Num a => Num (I a) where
  (*)         = liftA2 (*)
  (+)         = liftA2 (+)
  (-)         = liftA2 (-)
  abs         = fmap abs
  signum      = fmap signum
  fromInteger = pure . fromInteger

-- }}}

-- C {{{

data C :: * -> k -> * where
  C :: { getC :: r } -> C r a

deriving instance Eq   r => Eq   (C r a)
deriving instance Ord  r => Ord  (C r a)
deriving instance Show r => Show (C r a)

instance Witness p q r => Witness p q (C r a) where
  type WitnessC p q (C r a) = Witness p q r
  r \\ C a = r \\ a

instance Num r => Num (C r a) where
  C a * C b    = C $ a * b
  C a + C b    = C $ a + b
  C a - C b    = C $ a - b
  abs    (C a) = C $ abs a
  signum (C a) = C $ signum a
  fromInteger  = C . fromInteger

mapC :: (r -> s) -> C r a -> C s b
mapC f = C . f . getC

-- }}}

-- Flip {{{

newtype Flip p b a = Flip
  { getFlip :: p a b
  } deriving (Eq,Ord,Show)

flipTestEquality1 :: TestEquality (p c) => Flip p a c -> Flip p b c -> Maybe (a :~: b)
flipTestEquality1 (Flip a) (Flip b) = a =?= b

instance TestEquality1 p => TestEquality (Flip p b) where
  testEquality (Flip a) (Flip b) = a =??= b

instance Witness p q (f a b) => Witness p q (Flip f b a) where
  type WitnessC p q (Flip f b a) = Witness p q (f a b)
  r \\ Flip a = r \\ a

instance Known (p a) b => Known (Flip p b) a where
  type KnownC (Flip p b) a = Known (p a) b
  known = Flip known

mapFlip :: (f a b -> g c d) -> Flip f b a -> Flip g d c
mapFlip f = Flip . f . getFlip

-- }}}

-- Cur {{{

newtype Cur (p :: (k,l) -> *) :: k -> l -> * where
  Cur :: { getCur :: p (a#b) } -> Cur p a b

instance Known p (a#b) => Known (Cur p a) b where
  type KnownC (Cur p a) b = Known p (a#b)
  known = Cur known

instance Witness q r (p (a#b)) => Witness q r (Cur p a b) where
  type WitnessC q r (Cur p a b) = Witness q r (p (a#b))
  r \\ Cur p = r \\ p

mapCur :: (p '(a,b) -> q '(c,d)) -> Cur p a b -> Cur q c d
mapCur f = Cur . f . getCur

-- }}}

-- Uncur {{{

data Uncur (p :: k -> l -> *) :: (k,l) -> * where
  Uncur :: { getUncur :: p a b } -> Uncur p (a#b)

instance (Known (p a) b,q ~ (a#b)) => Known (Uncur p) q where
  type KnownC (Uncur p) q = Known (p (Fst q)) (Snd q)
  known = Uncur known

instance (Witness r s (p a b),q ~ (a#b)) => Witness r s (Uncur p q) where
  type WitnessC r s (Uncur p q) = Witness r s (p (Fst q) (Snd q))
  r \\ Uncur p = r \\ p

mapUncur :: (p (Fst a) (Snd a) -> q b c) -> Uncur p a -> Uncur q '(b,c)
mapUncur f (Uncur a) = Uncur $ f a

-- }}}

-- Cur3 {{{

newtype Cur3 (p :: (k,l,m) -> *) :: k -> l -> m -> * where
  Cur3 :: { getCur3 :: p '(a,b,c) } -> Cur3 p a b c

instance Known p '(a,b,c) => Known (Cur3 p a b) c where
  type KnownC (Cur3 p a b) c = Known p '(a,b,c)
  known = Cur3 known

instance Witness q r (p '(a,b,c)) => Witness q r (Cur3 p a b c) where
  type WitnessC q r (Cur3 p a b c) = Witness q r (p '(a,b,c))
  r \\ Cur3 p = r \\ p

mapCur3 :: (p '(a,b,c) -> q '(d,e,f)) -> Cur3 p a b c -> Cur3 q d e f
mapCur3 f = Cur3 . f . getCur3

-- }}}

-- Uncur3 {{{

data Uncur3 (p :: k -> l -> m -> *) :: (k,l,m) -> * where
  Uncur3 :: { getUncur3 :: p a b c } -> Uncur3 p '(a,b,c)

instance (Known (p a b) c,q ~ '(a,b,c)) => Known (Uncur3 p) q where
  type KnownC (Uncur3 p) q = Known (p (Fst3 q) (Snd3 q)) (Thd3 q)
  known = Uncur3 known

instance (Witness r s (p a b c),q ~ '(a,b,c)) => Witness r s (Uncur3 p q) where
  type WitnessC r s (Uncur3 p q) = Witness r s (p (Fst3 q) (Snd3 q) (Thd3 q))
  r \\ Uncur3 p = r \\ p

mapUncur3 :: (p (Fst3 x) (Snd3 x) (Thd3 x) -> q d e f) -> Uncur3 p x -> Uncur3 q '(d,e,f)
mapUncur3 f (Uncur3 a) = Uncur3 $ f a

-- }}}

-- Join {{{

newtype Join f a = Join
  { getJoin :: f a a
  }

deriving instance Eq   (f a a) => Eq   (Join f a)
deriving instance Ord  (f a a) => Ord  (Join f a)
deriving instance Show (f a a) => Show (Join f a)

instance Known (f a) a => Known (Join f) a where
  type KnownC (Join f) a = Known (f a) a
  known = Join known

instance Witness p q (f a a) => Witness p q (Join f a) where
  type WitnessC p q (Join f a) = Witness p q (f a a)
  r \\ Join a = r \\ a

mapJoin :: (f a a -> g b b) -> Join f a -> Join g b
mapJoin f = Join . f . getJoin

-- }}}

