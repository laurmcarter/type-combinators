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
-- Module      :  Type.Family.Bool
-- Copyright   :  Copyright (C) 2015 Kyle Carter
-- License     :  BSD3
--
-- Maintainer  :  Kyle Carter <kylcarte@indiana.edu>
-- Stability   :  experimental
-- Portability :  RankNTypes
--
-- Convenient type families for working with type-level @Bool@s.
----------------------------------------------------------------------------

module Type.Family.Bool
  ( module Type.Family.Bool
  , module Exports
  ) where

import Type.Family.Constraint
import Type.Class.Witness as Exports (type (==))
import Data.Type.Bool as Exports (type Not, type (||), type (&&))

type family BoolC (b :: Bool) :: Constraint where
  BoolC True  = ØC
  BoolC False = Fail

type a ==> b = Not a || b
infixr 1 ==>

type a <==> b = a == b
infixr 1 <==>

type a ^^ b = (a || b) && Not (a && b)
infixr 4 ^^

