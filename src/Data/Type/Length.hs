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

module Data.Type.Length where

import Type.Class.Known
import Type.Family.List

data Length :: [k] -> * where
  LZ :: Length Ø
  LS :: !(Length as) -> Length (a :< as)

lOdd, lEven :: Length as -> Bool
lOdd = \case
  LZ   -> False
  LS l -> lEven l
lEven = \case
  LZ   -> True
  LS l -> lOdd l

deriving instance Eq   (Length as)
deriving instance Ord  (Length as)
deriving instance Show (Length as)

instance Known Length Ø where
  known = LZ

instance Known Length as => Known Length (a :< as) where
  type KnownC Length (a :< as) = Known Length as
  known = LS known

