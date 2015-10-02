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

module Data.Type.Index where

import Type.Class.HFunctor
import Type.Class.Known
import Type.Family.List
import Type.Family.Nat

data Index :: [k] -> k -> * where
  IZ :: Index (a :< as) a
  IS :: !(Index as a) -> Index (b :< as) a

deriving instance Eq   (Index as a)
deriving instance Ord  (Index as a)
deriving instance Show (Index as a)

class Elem (as :: [k]) (a :: k) where
  elemIndex :: Index as a

instance {-# OVERLAPPING #-} Elem (a :< as) a where
  elemIndex = IZ

instance {-# OVERLAPPABLE #-} Elem as a => Elem (b :< as) a where
  elemIndex = IS elemIndex

instance {-# OVERLAPPING #-} Known (Index (a :< as)) a where
  known = IZ

instance {-# OVERLAPPABLE #-} Known (Index as) a => Known (Index (b :< as)) a where
  known = IS known

