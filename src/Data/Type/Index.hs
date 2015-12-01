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

-- import Type.Class.Categories
import Type.Class.Known
import Type.Class.Witness
import Type.Family.List

{-
newtype Permutation :: [k] -> [k] -> * where
  Perm :: { getPerm :: forall x. Index as x <-> Index bs x }
       -> Permutation as bs

instance Category Permutation where
  id    = Perm $ id
  g . f = Perm $ getPerm g . getPerm f

instance Symmetric Permutation where
  symm (Perm p) = Perm $ symm p

liftPerm :: Permutation as bs -> Permutation (a :< as) (a :< bs)
liftPerm (Perm p) = Perm $ liftIndex (fwd p) <-> liftIndex (bwd p)
-}

liftIndex :: (Index as a -> Index bs a) -> Index (b :< as) a -> Index (b :< bs) a
liftIndex f = \case
  IZ   -> IZ
  IS x -> IS $ f x

class Indexed (r :: *) (s :: *) (as :: [k]) (bs :: [k])
  | r -> as , s -> bs
  , r as bs -> s
  , s as bs -> r where
  mapIndex :: (forall x. Index as x -> Index bs x) -> r -> s

-- Index {{{

data Index :: [k] -> k -> * where
  IZ :: Index (a :< as) a
  IS :: !(Index as a) -> Index (b :< as) a

deriving instance Eq   (Index as a)
deriving instance Ord  (Index as a)
deriving instance Show (Index as a)

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

ixNil :: Index Ø a -> Void
ixNil = impossible

-- }}}

-- Index2 {{{

data Index2 :: [k] -> [l] -> k -> l -> * where
  IZ2 :: Index2 (a :< as) (b :< bs) a b
  IS2 :: !(Index2 as bs a b)
      -> Index2 (c :< as) (d :< bs) a b

deriving instance Eq   (Index2 as bs a b)
deriving instance Ord  (Index2 as bs a b)
deriving instance Show (Index2 as bs a b)

ix2NilL :: Index2 Ø bs a b -> Void
ix2NilL = impossible

ix2NilR :: Index2 as Ø a b -> Void
ix2NilR = impossible

elimIndex2 :: ( forall   xs   ys. p (a :< xs) (b :< ys) a b)
           -> ( forall x xs y ys.
                Index2 xs ys a b
             -> p xs ys a b
             -> p (x :< xs) (y :< ys) a b
              )
           -> Index2 as bs a b
           -> p as bs a b
elimIndex2 z s = \case
  IZ2   -> z
  IS2 x -> s x $ elimIndex2 z s x

-- }}}

-- Elem {{{

type a ∈ as = Elem as a
infix 6 ∈


class Elem (as :: [k]) (a :: k) where
  elemIndex :: Index as a

instance {-# OVERLAPPING #-} Elem (a :< as) a where
  elemIndex = IZ

instance {-# OVERLAPPABLE #-} Elem as a => Elem (b :< as) a where
  elemIndex = IS elemIndex


instance {-# OVERLAPPING #-} Known (Index (a :< as)) a where
  known = IZ

instance {-# OVERLAPPABLE #-} Known (Index as) a => Known (Index (b :< as)) a where
  known = IS known

-- }}}

