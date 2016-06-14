{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Type.Subset
-- Copyright   :  Copyright (C) 2015 Kyle Carter
-- License     :  BSD3
--
-- Maintainer  :  Kyle Carter <kylcarte@indiana.edu>
-- Stability   :  experimental
-- Portability :  RankNTypes
--
-- A @singleton@-esque type for representing subsets of a type level list.
--
-----------------------------------------------------------------------------

module Data.Type.Subset
  ( module Data.Type.Subset
  , module Exports
  ) where

-- import Data.Type.Quantifier
import Type.Class.Higher
import Type.Class.Known
import Type.Class.Witness
import Type.Family.List
import Data.Type.Index
import Data.Type.Length
import Data.Type.Product as Exports (Prod(..))
import Data.Type.Product (index)
import Data.Type.Sum (Sum(..),prj)
import Control.Applicative ((<|>))

type Subset as = Prod (Index as)

subNil :: Subset Ø as -> (as :~: Ø)
subNil = \case
  Ø      -> Refl
  x :< _ -> ixNil x

type as ⊆ bs = Every (Elem bs) as
infix 4 ⊆

subRefl :: Known Length as
  => Subset as as
subRefl = go known
  where
  go :: Length xs -> Subset xs xs
  go = \case
    LZ   -> Ø
    LS l -> IZ :< map1 IS (go l)

subTrans :: Subset as bs -> Subset bs cs -> Subset as cs
subTrans s = map1 $ subIx s

subProd :: Subset as bs -> Prod f as -> Prod f bs
subProd = \case
  Ø      -> pure Ø
  x :< s -> (:<) <$> index x <*> subProd s

subSum :: Subset as bs -> Sum f as -> Maybe (Sum f bs)
subSum = \case
  Ø      -> pure Nothing
  x :< s -> \t -> (InL <$> (prj t \\ x))
              <|> (InR <$> subSum s t)

subIx :: Subset as bs -> Index bs x -> Index as x
subIx = \case
  Ø      -> ixNil
  x :< s -> \case
    IZ   -> x
    IS y -> subIx s y

subExt :: Known Length as => (forall x. Index as x -> Index bs x) -> Subset bs as
subExt f = subExtBy f known

subExtBy :: (forall x. Index as x -> Index bs x) -> Length as -> Subset bs as
subExtBy f = \case
  LZ   -> Ø
  LS l -> f IZ :< subExtBy (f . IS) l

