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
-- Module      :  Data.Type.Length
-- Copyright   :  Copyright (C) 2015 Kyle Carter
-- License     :  BSD3
--
-- Maintainer  :  Kyle Carter <kylcarte@indiana.edu>
-- Stability   :  experimental
-- Portability :  RankNTypes
--
-- A @singleton@-esque type for representing lengths of type-level lists,
-- irrespective of the actual types in that list.
--
-----------------------------------------------------------------------------

module Data.Type.Length where

import Type.Class.Known
import Type.Family.List

data Length :: [k] -> * where
  LZ :: Length Ø
  LS :: !(Length as) -> Length (a :< as)

deriving instance Eq   (Length as)
deriving instance Ord  (Length as)
deriving instance Show (Length as)

instance Known Length Ø where
  known = LZ

instance Known Length as => Known Length (a :< as) where
  type KnownC Length (a :< as) = Known Length as
  known = LS known

elimLength :: p Ø
           -> (forall x xs. Length xs -> p xs -> p (x :< xs))
           -> Length as
           -> p as
elimLength z s = \case
  LZ   -> z
  LS l -> s l $ elimLength z s l

lOdd, lEven :: Length as -> Bool
lOdd = \case
  LZ   -> False
  LS l -> lEven l
lEven = \case
  LZ   -> True
  LS l -> lOdd l

