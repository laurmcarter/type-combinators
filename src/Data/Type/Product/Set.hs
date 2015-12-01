{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
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
-- Module      :  Data.Type.Product.Set
-- Copyright   :  Copyright (C) 2015 Kyle Carter
-- License     :  BSD3
--
-- Maintainer  :  Kyle Carter <kylcarte@indiana.edu>
-- Stability   :  experimental
-- Portability :  RankNTypes
--
-- Types and functions for treating type-level lists as sets.
--
-----------------------------------------------------------------------------

module Data.Type.Product.Set where

import Data.Type.Product
import Data.Type.Index
import Data.Type.Length
import Type.Class.Known
import Type.Class.Witness
import Type.Class.Categories
import Type.Family.List

import Prelude hiding (id,(.))
import Control.Category

-- Subset {{{

data Subset :: [k] -> [k] -> * where
  SubRefl :: Subset as as
  SubNil  :: Subset as Ø
  SubCons :: !(Index  as b)
          -> !(Subset as bs)
          -> Subset as (b :< bs)

instance Category Subset where
  id  = SubRefl
  (.) = \case
    SubRefl      -> id
    SubNil       -> pure SubNil
    SubCons b bs -> SubCons <$> (`subIndex` b) <*> (bs .)

type SetEq = Bij Subset

byIndex :: Known Length bs => (forall a. Index bs a -> Index as a) -> Subset as bs
byIndex = byIndex' known

byIndex' :: Length bs -> (forall a. Index bs a -> Index as a) -> Subset as bs
byIndex' l f = case l of
  LZ    -> SubNil
  LS l' -> SubCons (f IZ) $ byIndex' l' $ f . IS

subIndex :: Subset as bs -> Index bs a -> Index as a
subIndex = \case
  SubRefl      -> id
  SubNil       -> absurd . ixNil
  SubCons x xs -> \case
    IZ   -> x
    IS y -> subIndex xs y

subset :: Subset as bs -> Prod f as -> Prod f bs
subset = \case
  SubRefl      -> id
  SubNil       -> pure Ø
  SubCons b bs -> (:<) <$> index b <*> subset bs

setEq :: SetEq as bs -> Prod f as -> Prod f bs
setEq = subset . fwd

-- }}}

