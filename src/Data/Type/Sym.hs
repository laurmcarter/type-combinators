{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
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
-- Module      :  Data.Type.Sym
-- Copyright   :  Copyright (C) 2015 Kyle Carter
-- License     :  BSD3
--
-- Maintainer  :  Kyle Carter <kylcarte@indiana.edu>
-- Stability   :  experimental
-- Portability :  RankNTypes
--
-- A @singleton@-esque type for representing type-level Symbols.
--
-----------------------------------------------------------------------------

module Data.Type.Sym where

import Data.Type.Boolean
import Type.Class.Higher
import Type.Class.Known
import Type.Class.Witness
import Type.Family.Constraint
import Type.Family.Symbol
import Data.Proxy

data Sym :: Symbol -> * where
  Sym :: KnownSymbol x => Sym x

deriving instance Eq   (Sym x)
deriving instance Ord  (Sym x)

instance Show (Sym x) where
  showsPrec d x = showParen (d > 0)
    $ showString "Sym "
    . shows (symbol x)

instance Eq1   Sym
instance Ord1  Sym
instance Show1 Sym

instance TestEquality Sym where
  testEquality Sym Sym = sameSymbol Proxy Proxy

instance KnownSymbol x => Known Sym x where
  type KnownC Sym x = KnownSymbol x
  known = Sym

instance Witness ØC (KnownSymbol x) (Sym x) where
  r \\ Sym = r

symbol :: Sym x -> String
symbol x = symbolVal x \\ x

