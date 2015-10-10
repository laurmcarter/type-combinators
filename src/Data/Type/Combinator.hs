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
-- left unnest 'LL', right unnest 'RR', the @S Combinator@ 'SS',
-- etc.
--
-----------------------------------------------------------------------------

module Data.Type.Combinator where

import Type.Class.HFunctor
import Type.Class.Known
import Type.Class.Witness

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

data ((f :: m -> *) :..: (g :: k -> l -> m)) :: k -> l -> * where
  Comp2 :: f (g a b) -> (f :..: g) a b
infixr 6 :..:

deriving instance Eq   (f (g a b)) => Eq   ((f :..: g) a b)
deriving instance Ord  (f (g a b)) => Ord  ((f :..: g) a b)
deriving instance Show (f (g a b)) => Show ((f :..: g) a b)

instance Witness p q (f (g a b)) => Witness p q ((f :..: g) a b) where
  type WitnessC p q ((f :..: g) a b) = Witness p q (f (g a b))
  r \\ Comp2 a = r \\ a

-- }}}

-- IT {{{

data IT :: (k -> *) -> k -> * where
  IT :: { getIT :: f a } -> IT f a

deriving instance Eq   (f a) => Eq   (IT f a)
deriving instance Ord  (f a) => Ord  (IT f a)
deriving instance Show (f a) => Show (IT f a)

instance HFunctor IT where
  map' f = IT . f . getIT

instance HFoldable IT where
  foldMap' f = f . getIT

instance HTraversable IT where
  traverse' f = fmap IT . f . getIT

instance Witness p q (f a) => Witness p q (IT f a) where
  type WitnessC p q (IT f a) = Witness p q (f a)
  r \\ IT a = r \\ a

instance Num (f a) => Num (IT f a) where
  IT a * IT b   = IT $ a * b
  IT a + IT b   = IT $ a + b
  IT a - IT b   = IT $ a - b
  abs    (IT a) = IT $ abs a
  signum (IT a) = IT $ signum a
  fromInteger   = IT . fromInteger

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

-- LL {{{

newtype LL (a :: k) (f :: l -> *) (g :: k -> l) = LL
  { getLL :: f (g a)
  }

deriving instance Eq   (f (g a)) => Eq   (LL a f g)
deriving instance Ord  (f (g a)) => Ord  (LL a f g)
deriving instance Show (f (g a)) => Show (LL a f g)

instance HFunctor (LL a) where
  map' f = LL . f . getLL

instance HFoldable (LL a) where
  foldMap' f = f . getLL

instance HTraversable (LL a) where
  traverse' f = fmap LL . f . getLL

instance Witness p q (f (g a)) => Witness p q (LL a f g) where
  type WitnessC p q (LL a f g) = Witness p q (f (g a))
  r \\ LL a = r \\ a

-- }}}

-- RR {{{

newtype RR (g :: k -> l) (f :: l -> *) (a :: k) = RR
  { getRR :: f (g a)
  }

deriving instance Eq   (f (g a)) => Eq   (RR g f a)
deriving instance Ord  (f (g a)) => Ord  (RR g f a)
deriving instance Show (f (g a)) => Show (RR g f a)

instance HFunctor (RR g) where
  map' f = RR . f . getRR

instance HFoldable (RR g) where
  foldMap' f = f . getRR

instance HTraversable (RR g) where
  traverse' f = fmap RR . f . getRR

instance Witness p q (f (g a)) => Witness p q (RR g f a) where
  type WitnessC p q (RR g f a) = Witness p q (f (g a))
  r \\ RR a = r \\ a

-- }}}

-- SS {{{

newtype SS (f :: k -> l -> *) (g :: k -> l) :: k -> * where
  SS :: { getSS :: f a (g a) } -> SS f g a

deriving instance Eq   (f a (g a)) => Eq   (SS f g a)
deriving instance Ord  (f a (g a)) => Ord  (SS f g a)
deriving instance Show (f a (g a)) => Show (SS f g a)

instance Witness p q (f a (g a)) => Witness p q (SS f g a) where
  type WitnessC p q (SS f g a) = Witness p q (f a (g a))
  r \\ SS a = r \\ a

-- }}}

-- CT {{{

data CT :: * -> (k -> *) -> l -> * where
  CT :: { getCT :: r } -> CT r f a

deriving instance Eq   r => Eq   (CT r f a)
deriving instance Ord  r => Ord  (CT r f a)
deriving instance Show r => Show (CT r f a)

instance HFunctor (CT r) where
  map' _ (CT r) = CT r

instance HFoldable (CT r) where
  foldMap' _ _ = mempty

instance HTraversable (CT r) where
  traverse' _ (CT r) = pure $ CT r

instance Witness p q r => Witness p q (CT r f a) where
  type WitnessC p q (CT r f a) = Witness p q r
  r \\ CT a = r \\ a

instance Num r => Num (CT r f a) where
  CT a * CT b   = CT $ a * b
  CT a + CT b   = CT $ a + b
  CT a - CT b   = CT $ a - b
  abs    (CT a) = CT $ abs a
  signum (CT a) = CT $ signum a
  fromInteger   = CT . fromInteger

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
  

-- }}}

-- Flip {{{

newtype Flip p b a = Flip
  { getFlip :: p a b
  } deriving (Eq,Ord,Show)

instance Known (p a) b => Known (Flip p b) a where
  type KnownC (Flip p b) a = Known (p a) b
  known = Flip known

instance Witness p q (f a b) => Witness p q (Flip f b a) where
  type WitnessC p q (Flip f b a) = Witness p q (f a b)
  r \\ Flip a = r \\ a

flipped :: (f a b -> g c d) -> Flip f b a -> Flip g d c
flipped f = Flip . f . getFlip

-- }}}

