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
-- Module      :  Data.Type.Index
-- Copyright   :  Copyright (C) 2015 Kyle Carter
-- License     :  BSD3
--
-- Maintainer  :  Kyle Carter <kylcarte@indiana.edu>
-- Stability   :  experimental
-- Portability :  RankNTypes
--
-- A @singleton@-esque type for representing indices in a type-level list.
--
-----------------------------------------------------------------------------

module Data.Type.Index where

-- import Data.Type.Quantifier
import Type.Class.Higher
import Type.Class.Known
import Type.Class.Witness
import Type.Family.Constraint
import Type.Family.List

data Index :: [k] -> k -> * where
  IZ :: Index (a :< as) a
  IS :: !(Index as a) -> Index (b :< as) a

deriving instance Eq   (Index as a)
deriving instance Ord  (Index as a)
deriving instance Show (Index as a)

instance Eq1   (Index as)
instance Ord1  (Index as)
instance Show1 (Index as)

instance Read2 Index where
  readsPrec2 d = readParen (d > 10) $ \s0 ->
    [ (Some2 IZ,s1)
    | ("IZ",s1) <- lex s0
    ] ++
    [ (i >>-- Some2 . IS,s2)
    | ("IS",s1) <- lex s0
    , (i,s2)    <- readsPrec2 11 s1
    ]

instance TestEquality (Index as) where
  testEquality = \case
    IZ -> \case
      IZ -> qed
      _  -> Nothing
    IS x -> \case
      IS y -> x =?= y //? qed
      _    -> Nothing

elimIndex :: (forall   xs. p (a :< xs) a)
          -> (forall x xs. Index xs a -> p xs a -> p (x :< xs) a)
          -> Index as a
          -> p as a
elimIndex z s = \case
  IZ   -> z
  IS x -> s x $ elimIndex z s x

ixNil :: Index Ø a -> b
ixNil = absurd . impossible

onIxPred :: (Index as a -> Index bs a) -> Index (b :< as) a -> Index (b :< bs) a
onIxPred f = \case
  IZ   -> IZ
  IS x -> IS $ f x

type a ∈ as = Elem as a
infix 6 ∈

class Elem (as :: [k]) (a :: k) where
  elemIndex :: Index as a

instance {-# OVERLAPPING #-} Elem (a :< as) a where
  elemIndex   = IZ

instance {-# OVERLAPPABLE #-} Elem as a => Elem (b :< as) a where
  elemIndex = IS elemIndex

instance Witness ØC (Elem as a) (Index as a) where
  (\\) r = \case
    IZ   -> r
    IS x -> r \\ x

instance (a ∈ as) => Known (Index as) a where
  type KnownC (Index as) a = (a ∈ as)
  known = elemIndex

class EveryC c as => Every (c :: k -> Constraint) (as :: [k]) where
  type EveryC c as :: Constraint
  every :: Index as a -> Wit (c a)

instance Every c Ø where
  type EveryC c Ø = ØC
  every = ixNil

instance (c a, Every c as) => Every c (a :< as) where
  type EveryC c (a :< as) = (c a, Every c as)
  every = \case
    IZ   -> Wit
    IS x -> every x

class ListC ((c <$> xs) <&> y)
  => Every2 (c :: k -> l -> Constraint) (xs :: [k]) (y :: l) where
  every2 :: Index xs x -> Wit (c x y)

instance Every2 c Ø y where
  every2 = ixNil

instance (c x y, Every2 c xs y) => Every2 c (x :< xs) y where
  every2 = \case
    IZ   -> Wit
    IS x -> every2 x



