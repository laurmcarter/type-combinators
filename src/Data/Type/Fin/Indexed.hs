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
-- Module      :  Data.Type.Fin.Indexed
-- Copyright   :  Copyright (C) 2015 Kyle Carter
-- License     :  BSD3
--
-- Maintainer  :  Kyle Carter <kylcarte@indiana.edu>
-- Stability   :  experimental
-- Portability :  RankNTypes
--
-- A Fin type additionally indexed by its value.
--
-----------------------------------------------------------------------------

module Data.Type.Fin.Indexed where

import Data.Type.Length
import Data.Type.Index
import Data.Type.Nat
import Type.Class.Witness
import Type.Family.Constraint
import Type.Family.List
import Type.Family.Nat
import Data.Type.Quantifier

data IFin :: N -> N -> * where
  IFZ :: IFin (S x) Z
  IFS :: !(IFin x y)
      -> IFin (S x) (S y)

data IxFin :: [k] -> k -> * where
  IxFin :: (Ix x as ~ a) => IFin (Len as) x -> IxFin as a

ixFin :: Index as a -> IxFin as a
ixFin = \case
  IZ   -> IxFin IFZ
  IS i -> case ixFin i of
    IxFin n -> IxFin $ IFS n

