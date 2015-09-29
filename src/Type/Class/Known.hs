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

module Type.Class.Known where

import Type.Family.Constraint
import Type.Family.List

import Data.Type.Equality

class KnownC f a => Known (f :: k -> *) (a :: k) where
  type KnownC f a :: Constraint
  type KnownC (f :: k -> *) (a :: k) = ØC
  known :: f a

instance (a ~ b) => Known ((:~:) a) b where
  type KnownC ((:~:) a) b = (a ~ b)
  known = Refl

