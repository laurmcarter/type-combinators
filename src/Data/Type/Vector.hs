{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
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
-- 'Vec' and its combinator analog 'VecT' represent lists
-- of known length, characterized by the index @(n :: N)@ in
-- @'Vec' n a@ or @'VecT' n f a@.
--
-- The classic example used ad nauseum for type-level programming.
--
-- The operations on 'Vec' and 'VecT' correspond to the type level arithmetic
-- operations on the kind 'N'.
--
-----------------------------------------------------------------------------

module Data.Type.Vector where

import Data.Type.Combinator
import Data.Type.Fin
import Data.Type.Length
import Data.Type.Nat
import Data.Type.Product (Prod(..),curry',pattern (:>))

import Type.Class.Higher
import Type.Class.Known
import Type.Class.Witness

import Type.Family.Constraint
import Type.Family.List
import Type.Family.Nat

import qualified Data.List as L
import Data.Monoid

data VecT (n :: N) (f :: k -> *) :: k -> * where
  ØV   :: VecT Z f a
  (:*) :: !(f a) -> !(VecT n f a) -> VecT (S n) f a
infixr 4 :*

elimVecT :: p Z
       -> (forall x. f a -> p x -> p (S x))
       -> VecT n f a
       -> p n
elimVecT z s = \case
  ØV      -> z
  a :* as -> s a $ elimVecT z s as

elimV :: p Z
      -> (forall x. a -> p x -> p (S x))
      -> Vec n a
      -> p n
elimV z s = elimVecT z $ s . getI

type Vec n = VecT n I
pattern (:+) :: a -> Vec n a -> Vec (S n) a
pattern a :+ as = I a :* as
infixr 4 :+

deriving instance Eq   (f a) => Eq   (VecT n f a)
deriving instance Ord  (f a) => Ord  (VecT n f a)
deriving instance Show (f a) => Show (VecT n f a)

(.++) :: VecT x f a -> VecT y f a -> VecT (x + y) f a
(.++) = \case
  ØV      -> id
  a :* as -> (a :*) . (as .++)
infixr 5 .++

vrep :: forall n f a. Known Nat n => f a -> VecT n f a
vrep a = go (known :: Nat n)
  where
  go :: Nat x -> VecT x f a
  go = \case
    Z_   -> ØV
    S_ x -> a :* go x

head' :: VecT (S n) f a -> f a
head' (a :* _) = a

tail' :: VecT (S n) f a -> VecT n f a
tail' (_ :* as) = as

onTail :: (VecT m f a -> VecT n f a) -> VecT (S m) f a -> VecT (S n) f a
onTail f (a :* as) = a :* f as

vDel :: Fin n -> VecT n f a -> VecT (Pred n) f a
vDel = \case
  FZ   -> tail'
  FS x -> onTail (vDel x) \\ x

imap :: (Fin n -> f a -> g b) -> VecT n f a -> VecT n g b
imap f = \case
  ØV      -> ØV
  a :* as -> f FZ a :* imap (f . FS) as

ifoldMap :: Monoid m => (Fin n -> f a -> m) -> VecT n f a -> m
ifoldMap f = \case
  ØV      -> mempty
  a :* as -> f FZ a <> ifoldMap (f . FS) as

itraverse :: Applicative h => (Fin n -> f a -> h (g b)) -> VecT n f a -> h (VecT n g b)
itraverse f = \case
  ØV      -> pure ØV
  a :* as -> (:*) <$> f FZ a <*> itraverse (f . FS) as

index :: Fin n -> VecT n f a -> f a
index = \case
  FZ   -> head'
  FS x -> index x . tail'

index' :: Fin n -> Vec n a -> a
index' i = getI . index i

vmap :: (f a -> g b) -> VecT n f a -> VecT n g b
vmap f = \case
  ØV      -> ØV
  a :* as -> f a :* vmap f as

vap :: (f a -> g b -> h c) -> VecT n f a -> VecT n g b -> VecT n h c
vap f = \case
  ØV  -> \_ -> ØV
  a :* as -> \case
    b :* bs -> f a b :* vap f as bs

vfoldr :: (f a -> b -> b) -> b -> VecT n f a -> b
vfoldr s z = \case
  ØV      -> z
  a :* as -> s a $ vfoldr s z as

vfoldMap' :: (b -> b -> b) -> b -> (f a -> b) -> VecT n f a -> b
vfoldMap' j z f = \case
  ØV       -> z
  a :* ØV  -> f a
  a :* as  -> j (f a) $ vfoldMap' j z f as

vfoldMap :: Monoid m => (f a -> m) -> VecT n f a -> m
vfoldMap f = \case
  ØV      -> mempty
  a :* as -> f a <> vfoldMap f as

withVecT :: [f a] -> (forall n. VecT n f a -> r) -> r
withVecT as k = case as of
  []      -> k ØV
  a : as' -> withVecT as' $ \v -> k $ a :* v

withV :: [a] -> (forall n. Vec n a -> r) -> r
withV as k = withVecT (I <$> as) k

findV :: Eq a => a -> Vec n a -> Maybe (Fin n)
findV = findVecT . I

findVecT :: Eq (f a) => f a -> VecT n f a -> Maybe (Fin n)
findVecT a = \case
  ØV      -> Nothing
  b :* as -> if a == b
    then Just FZ
    else FS <$> findVecT a as

instance Functor1 (VecT n) where
  map1 f = \case
    ØV      -> ØV
    a :* as -> f a :* map1 f as

instance Foldable1 (VecT n) where
  foldMap1 f = \case
    ØV -> mempty
    a :* as -> f a <> foldMap1 f as

instance Traversable1 (VecT n) where
  traverse1 f = \case
    ØV      -> pure ØV
    a :* as -> (:*) <$> f a <*> traverse1 f as

instance Functor f => Functor (VecT n f) where
  fmap = vmap . fmap

instance (Applicative f, Known Nat n) => Applicative (VecT n f) where
  pure  = vrep . pure
  (<*>) = vap (<*>)

instance (Monad f, Known Nat n) => Monad (VecT n f) where
  v >>= f = imap (\x -> (>>= index x . f)) v

instance Foldable f => Foldable (VecT n f) where
  foldMap f = \case
    ØV      -> mempty
    a :* as -> foldMap f a <> foldMap f as

instance Traversable f => Traversable (VecT n f) where
  traverse f = \case
    ØV      -> pure ØV
    a :* as -> (:*) <$> traverse f a <*> traverse f as

{-
instance (Witness p q (f a), n ~ S x) => Witness p q (VecT n f a) where
  type WitnessC p q (VecT n f a) = Witness p q (f a)
  (\\) r = \case
    a :* _ -> r \\ a
    _      -> error "impossible type"
-}

instance Witness ØC (Known Nat n) (VecT n f a) where
  (\\) r = \case
    ØV      -> r
    _ :* as -> r \\ as

instance (Num (f a), Known Nat n) => Num (VecT n f a) where
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
  Matrix (n :< ns) = VecT n (Matrix ns)

vgen_ :: Known Nat n => (Fin n -> f a) -> VecT n f a
vgen_ = vgen known

vgen :: Nat n -> (Fin n -> f a) -> VecT n f a
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

diagonal :: VecT n (VecT n f) a -> VecT n f a
diagonal = imap index

vtranspose :: Known Nat n => VecT m (VecT n f) a -> VecT n (VecT m f) a
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

ppVec :: (VecT n ((->) String) String -> ShowS) -> (f a -> ShowS) -> VecT n f a -> ShowS
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
  (a:as',[]  ) -> f a      mempty  : mzipWith f as' []
  ([]   ,b:bs') -> f mempty b      : mzipWith f []  bs'
  (a:as',b:bs') -> f a      b      : mzipWith f as' bs'

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
instance (Additive f, Known Nat n) => Additive (VecT n f) where
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
instance (Affine f, Known Nat n) => Affine (VecT n f) where
  type Diff (VecT n f) = VecT n (Diff f)
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

instance (Metric f, Known Nat n) => Metric (VecT n f) where
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

