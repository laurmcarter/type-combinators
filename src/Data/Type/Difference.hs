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
-- Module      :  Data.Type.Difference
-- Copyright   :  Copyright (C) 2015 Kyle Carter
-- License     :  BSD3
--
-- Maintainer  :  Kyle Carter <kylcarte@indiana.edu>
-- Stability   :  experimental
-- Portability :  RankNTypes
--
-- A @singleton@-esque type for representing the removal of a subset of a type level list.
--
-----------------------------------------------------------------------------

module Data.Type.Difference where

-- import Data.Type.Quantifier
import Type.Class.Higher
import Type.Class.Known
import Type.Class.Witness
import Type.Family.Constraint
import Type.Family.List
import Data.Type.Index
import Data.Type.Length
import Data.Type.Subset
import Data.Type.Remove
import Data.Type.Product
import Data.Type.Sum
import Control.Arrow (first,left)

data Difference :: [k] -> [k] -> [k] -> * where
  ØD   :: Difference as Ø as
  (:-) :: !(Remove bs a cs)
       -> !(Difference cs as ds)
       -> Difference bs (a :< as) ds
infixr 5 :-

diffLen :: Difference as bs cs -> Length bs
diffLen = \case
  ØD     -> LZ
  _ :- d -> LS $ diffLen d

{-
deriving instance Eq   (Difference as bs cs)
deriving instance Ord  (Difference as bs cs)
deriving instance Show (Difference as bs cs)

instance Eq1   (Difference as bs)
instance Ord1  (Difference as bs)
instance Show1 (Difference as bs)

instance Eq2   (Difference as)
instance Ord2  (Difference as)
instance Show2 (Difference as)

instance Eq3   Difference
instance Ord3  Difference
instance Show3 Difference
-}

{-
instance Read3 Remove where
  readsPrec3 d = readParen (d > 10) $ \s0 ->
    [ (Some3 RZ,s1)
    | ("RZ",s1) <- lex s0
    ] ++
    [ (i >>--- Some3 . RS,s2)
    | ("RS",s1) <- lex s0
    , (i,s2)    <- readsPrec3 11 s1
    ]
-}

instance TestEquality (Difference as bs) where
  testEquality = \case
    ØD -> \case
      ØD -> qed
      _  -> Nothing
    r1 :- d1 -> \case
      r2 :- d2 -> r1 =?= r2 //? d1 =?= d2 //? qed
      _    -> Nothing

elimDifference :: (forall xs. p xs Ø xs)
               -> (forall x ws xs ys zs. Remove xs x ys -> Difference ys ws zs -> p ys ws zs -> p xs (x :< ws) zs)
               -> Difference as bs cs
               -> p as bs cs
elimDifference n c = \case
  ØD     -> n
  r :- d -> c r d $ elimDifference n c d

{-
diffSub :: Difference as bs cs -> Subset as bs
diffSub = \case
  ØD     -> Ø
  (r :: Remove as a ds) :- (d :: Difference ds es cs) -> x :< res
    where
    res :: Subset as es
    res = map1 f xs
    f :: Index ds x -> Index as x
    f = subIx $ remSub _ r
    x :: Index as a
    x = remIx r
    xs :: Subset ds es
    xs = diffSub d
-}

{-
subDiff :: Subset as bs -> Some (Difference as bs)
subDiff = \case
  Ø      -> Some ØD
  x :< s -> ixRem x >>- \r -> subDiff s >>- \d -> Some $ r :- _ d
-}

diffProd :: Difference as bs cs -> Prod f as -> (Prod f bs,Prod f cs)
diffProd = \case
  ØD     -> (,) Ø
  r :- d -> \as -> let
    (a,as') = remProd r as
    in first (a :<) $ diffProd d as'

diffSum :: Difference as bs cs -> Sum f as -> Either (Sum f bs) (Sum f cs)
diffSum = \case
  ØD     -> Right
  r :- d -> \as -> case remSum r as of
    Left  a  -> Left $ InL a
    Right bs -> left InR $ diffSum d bs

class WithoutAll (as :: [k]) (bs :: [k]) (cs :: [k]) | as bs -> cs where
  withoutAll :: Difference as bs cs

instance (cs ~ as) => WithoutAll as Ø cs where
  withoutAll = ØD

instance (Without as b cs, WithoutAll cs bs ds) => WithoutAll as (b :< bs) ds where
  withoutAll = without :- withoutAll

instance Witness ØC (WithoutAll as bs cs) (Difference as bs cs) where
  (\\) r = \case
    ØD     -> r
    x :- d -> r \\ x \\ d

instance WithoutAll as bs cs => Known (Difference as bs) cs where
  type KnownC (Difference as bs) cs = WithoutAll as bs cs
  known = withoutAll

