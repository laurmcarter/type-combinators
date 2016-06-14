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
-- Module      :  Data.Type.Remove
-- Copyright   :  Copyright (C) 2015 Kyle Carter
-- License     :  BSD3
--
-- Maintainer  :  Kyle Carter <kylcarte@indiana.edu>
-- Stability   :  experimental
-- Portability :  RankNTypes
--
-- A @singleton@-esque type for representing the removal of an element from a type level list.
--
-----------------------------------------------------------------------------

module Data.Type.Remove where

-- import Data.Type.Quantifier
import Type.Class.Higher
import Type.Class.Known
import Type.Class.Witness
import Type.Family.Constraint
import Type.Family.List
import Type.Family.Nat
import Data.Type.Length
import Data.Type.Index
import Data.Type.Subset
import Data.Type.Product
import Data.Type.Sum
import Control.Arrow (second,right)

data Remove :: [k] -> k -> [k] -> * where
  RZ :: Remove (a :< as) a as
  RS :: !(Remove as a bs)
     -> Remove (b :< as) a (b :< bs)

deriving instance Eq   (Remove as a bs)
deriving instance Ord  (Remove as a bs)
deriving instance Show (Remove as a bs)

instance Eq1   (Remove as a)
instance Ord1  (Remove as a)
instance Show1 (Remove as a)

instance Eq2   (Remove as)
instance Ord2  (Remove as)
instance Show2 (Remove as)

instance Eq3   Remove
instance Ord3  Remove
instance Show3 Remove

instance Read3 Remove where
  readsPrec3 d = readParen (d > 10) $ \s0 ->
    [ (Some3 RZ,s1)
    | ("RZ",s1) <- lex s0
    ] ++
    [ (i >>--- Some3 . RS,s2)
    | ("RS",s1) <- lex s0
    , (i,s2)    <- readsPrec3 11 s1
    ]

instance TestEquality (Remove as a) where
  testEquality = \case
    RZ -> \case
      RZ -> qed
      _  -> Nothing
    RS x -> \case
      RS y -> x =?= y //? qed
      _    -> Nothing

remLen :: Remove as a bs -> S (Len bs) :~: Len as
remLen = \case
  RZ   -> Refl
  RS r -> remLen r // Refl

elimRemove :: (forall xs. p (a :< xs) a xs)
           -> (forall x xs ys. Remove xs a ys -> p xs a ys -> p (x :< xs) a (x :< ys))
           -> Remove as a bs
           -> p as a bs
elimRemove z s = \case
  RZ   -> z
  RS r -> s r $ elimRemove z s r

remIx :: Remove as a bs -> Index as a
remIx = \case
  RZ   -> IZ
  RS r -> IS $ remIx r

remSub :: Length bs -> Remove as a bs -> Subset as bs
remSub = \case
  LZ   -> \case
    RZ -> Ø
  LS l -> \case
    RZ   -> IS IZ :< map1 (IS . IS) subRefl \\ l
    RS r -> IZ :< map1 IS (remSub l r)

ixRem :: Index as a -> Some (Remove as a)
ixRem = \case
  IZ   -> Some RZ
  IS x -> ixRem x >>- Some . RS

remProd :: Remove as a bs -> Prod f as -> (f a,Prod f bs)
remProd = \case
  RZ   -> (,) <$> head' <*> tail'
  RS r -> \(a :< as) -> second (a :<) $ remProd r as

remSum :: Remove as a bs -> Sum f as -> Either (f a) (Sum f bs)
remSum = \case
  RZ   -> \case
    InL a -> Left a
    InR b -> Right b
  RS r -> \case
    InL a -> Right $ InL a
    InR b -> right InR $ remSum r b

class Without (as :: [k]) (a :: k) (bs :: [k]) | as a -> bs where
  without :: Remove as a bs

instance {-# OVERLAPPING #-} (as ~ bs) => Without (a :< as) a bs where
  without = RZ

instance {-# OVERLAPPABLE #-} (cs ~ (b :< bs), Without as a bs) => Without (b :< as) a cs where
  without = RS without

instance Witness ØC (Without as a bs) (Remove as a bs) where
  (\\) r = \case
    RZ   -> r
    RS x -> r \\ x

instance (Without as a bs) => Known (Remove as a) bs where
  type KnownC (Remove as a) bs = Without as a bs
  known = without

