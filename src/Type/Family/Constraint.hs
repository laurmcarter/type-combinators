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
-- Module      :  Type.Family.Constraint
-- Copyright   :  Copyright (C) 2015 Kyle Carter
-- License     :  BSD3
--
-- Maintainer  :  Kyle Carter <kylcarte@indiana.edu>
-- Stability   :  experimental
-- Portability :  RankNTypes
--
-- Reexports the kind 'GHC.Exts.Constraint', as well as some
-- conveniences for working with 'Constraint's.
----------------------------------------------------------------------------

module Type.Family.Constraint
  ( module Type.Family.Constraint
  , Constraint
  ) where

import GHC.Exts (Constraint)

-- | The empty 'Constraint'.
type ØC   = (() :: Constraint)
type Fail = (True ~ False)

class IffC b t f => Iff (b :: Bool) (t :: Constraint) (f :: Constraint) where
  type IffC b t f :: Constraint
instance t => Iff True  t f where
  type IffC True  t f = t
instance f => Iff False t f where
  type IffC False t f = f

class d (c a) => Comp (d :: l -> Constraint) (c :: k -> l) (a :: k)
instance d (c a) => Comp d c a

