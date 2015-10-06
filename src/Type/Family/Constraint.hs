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

module Type.Family.Constraint
  ( module Type.Family.Constraint
  , Constraint
  ) where

import GHC.Exts (Constraint)

type ØC = (() :: Constraint)

class IffC b t f => Iff (b :: Bool) (t :: Constraint) (f :: Constraint) where
  type IffC b t f :: Constraint
instance t => Iff True  t f where
  type IffC True  t f = t
instance f => Iff False t f where
  type IffC False t f = f

