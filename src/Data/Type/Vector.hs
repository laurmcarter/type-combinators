{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
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
-- Module      :  Data.Type.Vector
-- Copyright   :  Copyright (C) 2015 Kyle Carter
-- License     :  BSD3
--
-- Maintainer  :  Kyle Carter <kylcarte@indiana.edu>
-- Stability   :  experimental
-- Portability :  RankNTypes
--
-- 'V' and its combinator analog 'VT' represent lists
-- of known length, characterized by the index @(n :: N)@ in
-- @'V' n a@ or @'VT' n f a@.
--
-- The classic example used ad nauseum for type-level programming.
--
-- The operations on 'V' and 'VT' correspond to the type level arithmetic
-- operations on the kind 'N'.
--
-----------------------------------------------------------------------------

module Data.Type.Vector where

import Data.Type.Combinator
import Data.Type.Fin
import Data.Type.Length
import Data.Type.Nat
import Data.Type.Product (Prod(..),curry',pattern (:>))

import Type.Class.HFunctor
import Type.Class.Known
import Type.Class.Witness

import Type.Family.Constraint
import Type.Family.List
import Type.Family.Nat

import Control.Applicative
import Control.Arrow
import Control.Monad (join)
import qualified Data.List as L
import Data.Monoid
import qualified Data.Foldable as F

data VT (n :: N) (f :: k -> *) :: k -> * where
  ØV   :: VT Z f a
  (:*) :: !(f a) -> !(VT n f a) -> VT (S n) f a
infixr 4 :*

type V n = VT n I
pattern (:+) :: a -> V n a -> V (S n) a
pattern a :+ as = I a :* as
infixr 4 :+

deriving instance Eq   (f a) => Eq   (VT n f a)
deriving instance Ord  (f a) => Ord  (VT n f a)
deriving instance Show (f a) => Show (VT n f a)

(.++) :: VT x f a -> VT y f a -> VT (x + y) f a
(.++) = \case
  ØV      -> id
  a :* as -> (a :*) . (as .++)
infixr 5 .++

vrep :: forall n f a. Known Nat n => f a -> VT n f a
vrep a = go (known :: Nat n)
  where
  go :: Nat x -> VT x f a
  go = \case
    Z_   -> ØV
    S_ x -> a :* go x

head' :: VT (S n) f a -> f a
head' (a :* _) = a

tail' :: VT (S n) f a -> VT n f a
tail' (_ :* as) = as

onTail :: (VT m f a -> VT n f a) -> VT (S m) f a -> VT (S n) f a
onTail f (a :* as) = a :* f as

vDel :: Fin n -> VT n f a -> VT (Pred n) f a
vDel = \case
  FZ   -> tail'
  FS x -> onTail (vDel x) \\ x

imap :: (Fin n -> f a -> g b) -> VT n f a -> VT n g b
imap f = \case
  ØV      -> ØV
  a :* as -> f FZ a :* imap (f . FS) as

ifoldMap :: Monoid m => (Fin n -> f a -> m) -> VT n f a -> m
ifoldMap f = \case
  ØV      -> mempty
  a :* as -> f FZ a <> ifoldMap (f . FS) as

itraverse :: Applicative h => (Fin n -> f a -> h (g b)) -> VT n f a -> h (VT n g b)
itraverse f = \case
  ØV      -> pure ØV
  a :* as -> (:*) <$> f FZ a <*> itraverse (f . FS) as

index :: Fin n -> VT n f a -> f a
index = \case
  FZ   -> head'
  FS x -> index x . tail'

vmap :: (f a -> g b) -> VT n f a -> VT n g b
vmap f = \case
  ØV      -> ØV
  a :* as -> f a :* vmap f as

vap :: (f a -> g b -> h c) -> VT n f a -> VT n g b -> VT n h c
vap f = \case
  ØV  -> \_ -> ØV
  a :* as -> \case
    b :* bs -> f a b :* vap f as bs
    _       -> error "impossible type"

vfoldr :: (f a -> b -> b) -> b -> VT n f a -> b
vfoldr s z = \case
  ØV      -> z
  a :* as -> s a $ vfoldr s z as

vfoldMap' :: (b -> b -> b) -> b -> (f a -> b) -> VT n f a -> b
vfoldMap' j z f = \case
  ØV       -> z
  a :* ØV  -> f a
  a :* as  -> j (f a) $ vfoldMap' j z f as

vfoldMap :: Monoid m => (f a -> m) -> VT n f a -> m
vfoldMap f = \case
  ØV      -> mempty
  a :* as -> f a <> vfoldMap f as

withVT :: [f a] -> (forall n. VT n f a -> r) -> r
withVT as k = case as of
  []     -> k ØV
  a : as -> withVT as $ \v -> k $ a :* v

withV :: [a] -> (forall n. V n a -> r) -> r
withV as k = withVT (I <$> as) k

findV :: Eq a => a -> V n a -> Maybe (Fin n)
findV = findVT . I

findVT :: Eq (f a) => f a -> VT n f a -> Maybe (Fin n)
findVT a = \case
  ØV      -> Nothing
  b :* as -> if a == b
    then Just FZ
    else FS <$> findVT a as

instance Functor f => Functor (VT n f) where
  fmap = vmap . fmap

instance (Applicative f, Known Nat n) => Applicative (VT n f) where
  pure  = vrep . pure
  (<*>) = vap (<*>)

instance (Monad f, Known Nat n) => Monad (VT n f) where
  v >>= f = imap (\x -> (>>= index x . f)) v

instance Foldable f => Foldable (VT n f) where
  foldMap f = \case
    ØV      -> mempty
    a :* as -> foldMap f a <> foldMap f as

instance Traversable f => Traversable (VT n f) where
  traverse f = \case
    ØV      -> pure ØV
    a :* as -> (:*) <$> traverse f a <*> traverse f as

{-
instance (Witness p q (f a), n ~ S x) => Witness p q (VT n f a) where
  type WitnessC p q (VT n f a) = Witness p q (f a)
  (\\) r = \case
    a :* _ -> r \\ a
    _      -> error "impossible type"
-}

instance Witness ØC (Known Nat n) (VT n f a) where
  (\\) r = \case
    ØV      -> r
    _ :* as -> r \\ as

instance (Num (f a), Known Nat n) => Num (VT n f a) where
  (*)         = vap (*)
  (+)         = vap (+)
  (-)         = vap (-)
  negate      = vmap negate
  abs         = vmap abs
  signum      = vmap signum
  fromInteger = vrep . fromInteger

newtype M ns a = M { getMatrix :: Matrix ns a }

deriving instance Eq   (Matrix ns a) => Eq   (M ns a)
deriving instance Ord  (Matrix ns a) => Ord  (M ns a)
deriving instance Show (Matrix ns a) => Show (M ns a)

instance Num (Matrix ns a) => Num (M ns a) where
  fromInteger  = M . fromInteger
  M a * M b    = M $ a * b
  M a + M b    = M $ a + b
  M a - M b    = M $ a - b
  abs (M a)    = M $ abs a
  signum (M a) = M $ signum a

type family Matrix (ns :: [N]) :: * -> * where
  Matrix Ø         = I
  Matrix (n :< ns) = VT n (Matrix ns)

vgen_ :: Known Nat n => (Fin n -> f a) -> VT n f a
vgen_ = vgen known

vgen :: Nat n -> (Fin n -> f a) -> VT n f a
vgen x f = case x of
  Z_   -> ØV
  S_ y -> f FZ :* vgen y (f . FS)

mgen_ :: Known (Prod Nat) ns => (Prod Fin ns -> a) -> M ns a
mgen_ = mgen known

mgen :: Prod Nat ns -> (Prod Fin ns -> a) -> M ns a
mgen ns f = case ns of
  Ø        -> M $ I $ f Ø
  n :< ns' -> M $ vgen n $ getMatrix . mgen ns' . curry' f

onMatrix :: (Matrix ms a -> Matrix ns b) -> M ms a -> M ns b
onMatrix f = M . f . getMatrix

diagonal :: VT n (VT n f) a -> VT n f a
diagonal = imap index

vtranspose :: Known Nat n => VT m (VT n f) a -> VT n (VT m f) a
vtranspose v = vgen_ $ \x -> vmap (index x) v

transpose :: Known Nat n => M (m :< n :< ns) a -> M (n :< m :< ns) a
transpose = onMatrix vtranspose

m0 :: M Ø Int
m0 = 1

m1 :: M '[N2] Int
m1 = 2

m2 :: M '[N2,N4] Int
m2 = 3

m3 :: M '[N2,N3,N4] (Int,Int,Int)
m3 = mgen_ $ \(x :< y :> z) -> (fin x,fin y,fin z)

m4 :: M '[N2,N3,N4,N5] (Int,Int,Int,Int)
m4 = mgen_ $ \(w :< x :< y :> z) -> (fin w,fin x,fin y,fin z)

ppVec :: (VT n ((->) String) String -> ShowS) -> (f a -> ShowS) -> VT n f a -> ShowS
ppVec pV pF = pV . vmap pF

ppMatrix :: forall ns a. (Show a, Known Length ns) => M ns a -> IO ()
ppMatrix = putStrLn . ($ "") . ppMatrix' (known :: Length ns) . getMatrix

ppMatrix' :: Show a => Length ns -> Matrix ns a -> ShowS
ppMatrix' = \case
  LZ   -> shows . getI
  LS l -> ppVec
    ( vfoldMap'
      ( if lEven l
        then zipLines $ \x y -> x . showChar '|'  . y
        else            \x y -> x . showChar '\n' . y
      ) (showString "[]") id
    ) $ ppMatrix' l

mzipWith :: Monoid a => (a -> a -> b) -> [a] -> [a] -> [b]
mzipWith f as bs = case (as,bs) of
  ([]  ,[]  ) -> []
  (a:as,[]  ) -> f a      mempty : mzipWith f as []
  ([]  ,b:bs) -> f mempty b      : mzipWith f [] bs
  (a:as,b:bs) -> f a      b      : mzipWith f as bs

zipLines :: (ShowS -> ShowS -> ShowS) -> ShowS -> ShowS -> ShowS
zipLines f a b = compose $ L.intersperse (showChar '\n') $ mzipWith
  (\(Endo x) (Endo y) -> f x y)
  (Endo . showString <$> lines (a ""))
  (Endo . showString <$> lines (b ""))

{-
juxtLines :: (ShowS -> ShowS -> ShowS) -> ShowS -> ShowS -> ShowS
juxtLines f a b = appEndo $ foldMap id $ mzip (\x y -> Endo $ f (appEndo x) (appEndo y)) as bs
  where
  as = map (Endo . showString) $ lines $ a ""
  bs = map (Endo . showString) $ lines $ b ""
-}

compose :: Foldable f => f (a -> a) -> a -> a
compose = appEndo . foldMap Endo

{-
-- Linear {{{

class Functor f => Additive f where
  zero   :: Num a => f a
  (^+^)  :: Num a => f a -> f a -> f a
  (^-^)  :: Num a => f a -> f a -> f a
  lerp   :: Num a =>   a -> f a -> f a -> f a
  liftU2 :: (a -> a -> a) -> f a -> f a -> f a
  liftI2 :: (a -> b -> c) -> f a -> f b -> f c
  --------
  default zero :: (Applicative f, Num a) => f a
  zero = pure 0
  (^+^)   = liftU2 (+)
  a ^-^ b = a ^+^ negated b
  lerp alpha a b = alpha *^ a ^+^ (1 - alpha) *^ b
  default liftU2 :: Applicative f => (a -> a -> a) -> f a -> f a -> f a
  liftU2 = liftA2
  default liftI2 :: Applicative f => (a -> b -> c) -> f a -> f b -> f c
  liftI2 = liftA2
infixl 6 ^+^, ^-^

instance Additive I
instance (Additive f, Known Nat n) => Additive (VT n f) where
  zero   = vrep zero
  liftU2 = vap . liftU2
  liftI2 = vap . liftI2

class Additive (Diff f) => Affine f where
  type Diff f :: * -> *
  type Diff f = f
  (.-.) :: Num a => f a -> f a -> Diff f a
  (.+^) :: Num a => f a -> Diff f a -> f a
  (.-^) :: Num a => f a -> Diff f a -> f a
  --------
  p .-^ d = p .+^ negated d
  default (.-.) :: (Affine f, Diff f ~ f, Num a) => f a -> f a -> Diff f a
  (.-.) = (^-^)
  default (.+^) :: (Affine f, Diff f ~ f, Num a) => f a -> f a -> Diff f a
  (.+^) = (^+^)
infixl 6 .-., .+^, .-^

instance Affine I
instance (Affine f, Known Nat n) => Affine (VT n f) where
  type Diff (VT n f) = VT n (Diff f)
  (.-.) = vap (.-.)
  (.+^) = vap (.+^)
  (.-^) = vap (.-^)

class Additive f => Metric f where
  dot       :: Num a => f a -> f a -> a
  quadrance :: Num a => f a -> a
  qd        :: Num a => f a -> f a -> a
  distance  :: Floating a => f a -> f a -> a
  norm      :: Floating a => f a -> a
  signorm   :: Floating a => f a -> f a
  --------
  default dot :: (Foldable f, Num a) => f a -> f a -> a
  dot       a b = F.sum $ liftI2 (*) a b
  quadrance     = join dot
  qd        a b = quadrance $ a ^-^ b
  distance  a b = norm $ a ^-^ b
  norm          = sqrt . quadrance
  signorm   a   = (/ norm a) <$> a

instance Metric I where
  dot (I a) (I b) = a * b

instance (Metric f, Known Nat n) => Metric (VT n f) where
  dot a b = getSum $ foldMap Sum $ vap ((I .) . dot) a b

(*^) :: (Functor f, Num a) => a -> f a -> f a
(*^) a = fmap (a*)
infixl 7 *^

negated :: (Functor f, Num a) => f a -> f a
negated = fmap negate

qdA :: (Affine f, Foldable (Diff f), Num a) => f a -> f a -> a
qdA a b = F.sum $ join (*) <$> a .-. b

distanceA :: (Affine f, Foldable (Diff f), Floating a) => f a -> f a -> a
distanceA a b = sqrt $ qdA a b

-- }}}
-}

