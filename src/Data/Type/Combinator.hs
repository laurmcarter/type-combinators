{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
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

-- import Data.Type.Quantifier
import Type.Class.Higher
import Type.Class.Known
import Type.Class.Witness
import Type.Family.Tuple

import Control.Applicative

data Comp1 (f :: l -> m -> *) (g :: k -> l) :: k -> m -> * where
  Comp1 :: { getComp1 :: !(f (g h) a)
           }
        -> Comp1 f g h a

instance (Functor1 f, Functor1 g) => Functor1 (Comp1 (f :: (l -> *) -> m -> *) (g :: (k -> *) -> l -> *)) where
  map1 f (Comp1 a) = Comp1 $ map1 (map1 f) a

{-
instance (IxFunctor1 i f, IxFunctor1 j g) => IxFunctor1 (IxComp i j) (Comp1 (f :: (l -> *) -> m -> *) (g :: (k -> *) -> l -> *)) where
  imap1 f = Comp1 . imap1 (\i -> imap1 $ \j -> f $ IxComp i j) . getComp1
-}

-- (:.:) {{{

newtype ((f :: l -> *) :.: (g :: k -> l)) (a :: k) = Comp
  { getComp :: f (g a)
  } deriving
  ( Eq , Ord , Show , Read
  )

instance Eq1 f => Eq1 (f :.: g) where
  Comp a `eq1` Comp b = a `eq1` b

instance Ord1 f => Ord1 (f :.: g) where
  Comp a `compare1` Comp b = a `compare1` b

instance Show1 f => Show1 (f :.: g) where
  showsPrec1 d (Comp a) = showParen (d > 10)
    $ showString "Comp "
    . showsPrec1 11 a

instance Witness p q (f (g a)) => Witness p q ((f :.: g) a) where
  type WitnessC p q ((f :.: g) a) = Witness p q (f (g a))
  r \\ Comp a = r \\ a

instance TestEquality f => TestEquality (f :.: g) where
  testEquality (Comp a) (Comp b) = a =?= b //? qed

instance TestEquality f => TestEquality1 ((:.:) f) where
  testEquality1 (Comp a) (Comp b) = a =?= b //? qed

-- }}}

-- I {{{

newtype I a = I
  { getI :: a
  } deriving
  ( Eq , Ord , Show
  , Functor , Foldable , Traversable
  )

instance Applicative I where
  pure = I
  I f <*> I a = I $ f a

instance Monad I where
  I a >>= f = f a

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

newtype C r a = C
  { getC :: r
  } deriving
  ( Eq , Ord , Show , Read
  , Functor , Foldable , Traversable
  )

instance Eq   r => Eq1   (C r)
instance Ord  r => Ord1  (C r)
instance Show r => Show1 (C r)

instance Read r => Read1 (C r) where
  readsPrec1 d = readParen (d > 10) $ \s0 ->
    [ (Some $ C r,s2)
    | ("C",s1) <- lex s0
    , (r,s2)   <- readsPrec 11 s1
    ]

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
  } deriving
  ( Eq , Ord , Show , Read
  )

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

newtype Cur (p :: (k,l) -> *) (a :: k) (b :: l) = Cur
  { getCur :: p (a#b)
  }

deriving instance Eq   (p (a#b)) => Eq   (Cur p a b)
deriving instance Ord  (p (a#b)) => Ord  (Cur p a b)
deriving instance Show (p (a#b)) => Show (Cur p a b)
deriving instance Read (p (a#b)) => Read (Cur p a b)

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

deriving instance Eq   (p (Fst x) (Snd x)) => Eq   (Uncur p x)
deriving instance Ord  (p (Fst x) (Snd x)) => Ord  (Uncur p x)
deriving instance Show (p (Fst x) (Snd x)) => Show (Uncur p x)
deriving instance (x ~ (a#b), Read (p a b)) => Read (Uncur p x)

instance Read2 p => Read1 (Uncur p) where
  readsPrec1 d = readParen (d > 10) $ \s0 ->
    [ (p >>-- Some . Uncur,s2)
    | ("Uncur",s1) <- lex s0
    , (p,s2)       <- readsPrec2 11 s1
    ]

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

newtype Cur3 (p :: (k,l,m) -> *) (a :: k) (b :: l) (c :: m) = Cur3
  { getCur3 :: p '(a,b,c)
  }

deriving instance Eq   (p '(a,b,c)) => Eq   (Cur3 p a b c)
deriving instance Ord  (p '(a,b,c)) => Ord  (Cur3 p a b c)
deriving instance Show (p '(a,b,c)) => Show (Cur3 p a b c)
deriving instance Read (p '(a,b,c)) => Read (Cur3 p a b c)

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

deriving instance Eq   (p (Fst3 x) (Snd3 x) (Thd3 x)) => Eq   (Uncur3 p x)
deriving instance Ord  (p (Fst3 x) (Snd3 x) (Thd3 x)) => Ord  (Uncur3 p x)
deriving instance Show (p (Fst3 x) (Snd3 x) (Thd3 x)) => Show (Uncur3 p x)
deriving instance (x ~ '(a,b,c), Read (p a b c)) => Read (Uncur3 p x)

instance Read3 p => Read1 (Uncur3 p) where
  readsPrec1 d = readParen (d > 10) $ \s0 ->
    [ (p >>--- Some . Uncur3,s2)
    | ("Uncur",s1) <- lex s0
    , (p,s2)       <- readsPrec3 11 s1
    ]

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
deriving instance Read (f a a) => Read (Join f a)

instance Eq2 f => Eq1 (Join f) where
  Join a `eq1` Join b = a `eq2` b

instance Ord2 f => Ord1 (Join f) where
  Join a `compare1` Join b = a `compare2` b

instance Show2 f => Show1 (Join f) where
  showsPrec1 d (Join a) = showParen (d > 10)
    $ showString "Join "
    . showsPrec2 11 a

instance Known (f a) a => Known (Join f) a where
  type KnownC (Join f) a = Known (f a) a
  known = Join known

instance Witness p q (f a a) => Witness p q (Join f a) where
  type WitnessC p q (Join f a) = Witness p q (f a a)
  r \\ Join a = r \\ a

mapJoin :: (f a a -> g b b) -> Join f a -> Join g b
mapJoin f = Join . f . getJoin

-- }}}

data Conj (t :: (k -> *) -> l -> *) (f :: k -> m -> *) :: l -> m -> * where
  Conj :: t (Flip f b) a
       -> Conj t f a b

{-
data Conj2 (t :: (k -> l -> *) -> m -> n -> *) (f :: k -> l -> o -> *) :: m -> n -> o -> * where
  Conj2 :: t 
       -> Conj2 t f a b c
-}

data LL (c :: k -> *) :: l -> (l -> k) -> * where
  LL :: { getLL :: c (f a)
        }
     -> LL c a f

data RR (c :: k -> *) :: (l -> k) -> l -> * where
  RR :: { getRR :: c (f a) }
     -> RR c f a

