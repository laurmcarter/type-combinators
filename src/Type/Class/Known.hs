{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
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
-- Module      :  Type.Class.Known
-- Copyright   :  Copyright (C) 2015 Kyle Carter
-- License     :  BSD3
--
-- Maintainer  :  Kyle Carter <kylcarte@indiana.edu>
-- Stability   :  experimental
-- Portability :  RankNTypes
--
-- The 'Known' class, among others in this library, use an associated
-- 'Constraint' to maintain a bidirectional chain of inference.
--
-- For instance, given evidence of @Known Nat n@, if @n@ later gets refined
-- to @n'@, we can correctly infer @Known Nat n'@, as per the type instance
-- defined for @KnownC Nat (S n')@.
----------------------------------------------------------------------------

module Type.Class.Known where

import Type.Family.Constraint

import Data.Type.Equality

-- | Each instance of 'Known' provides a canonical construction
-- of a type at a particular index.
--
-- Useful for working with singleton-esque GADTs.
class KnownC f a => Known (f :: k -> *) (a :: k) where
  type KnownC f a :: Constraint
  type KnownC (f :: k -> *) (a :: k) = ØC
  known :: f a

instance (a ~ b) => Known ((:~:) a) b where
  type KnownC ((:~:) a) b = (a ~ b)
  known = Refl

