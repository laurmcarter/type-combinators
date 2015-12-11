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

import Type.Class.Known
import Type.Class.Witness
import Type.Family.List

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

onIxPred :: (Index as a -> Index bs a) -> Index (b :< as) a -> Index (b :< bs) a
onIxPred f = \case
  IZ   -> IZ
  IS x -> IS $ f x

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

