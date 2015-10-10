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
-- Module      :  Type.Family.List
-- Copyright   :  Copyright (C) 2015 Kyle Carter
-- License     :  BSD3
--
-- Maintainer  :  Kyle Carter <kylcarte@indiana.edu>
-- Stability   :  experimental
-- Portability :  RankNTypes
--
-- Convenient aliases and type families for working with
-- type-level lists.
----------------------------------------------------------------------------

module Type.Family.List
  ( module Type.Family.List
  , (==)
  ) where

import Type.Family.Constraint
import Type.Family.Monoid

import Data.Type.Bool
import Data.Type.Equality

type Ø    = '[]
type (:<) = '(:)
infixr 5 :<

-- | Type-level singleton list.
type Only a = '[a]

-- | Appends two type-level lists.
type family (as :: [k]) ++ (bs :: [k]) :: [k] where
  Ø         ++ bs = bs
  (a :< as) ++ bs = a :< (as ++ bs)
infixr 5 ++

-- | Type-level list snoc.
type family (as :: [k]) >: (a :: k) :: [k] where
  Ø         >: a = Only a
  (b :< as) >: a = b :< (as >: a)
infixl 6 >:

type family Reverse (as :: [k]) :: [k] where
  Reverse  Ø        = Ø
  Reverse (a :< as) = Reverse as >: a

type family Init' (a :: k) (as :: [k]) :: [k] where
  Init' a Ø = Ø
  Init' a (b :< as) = a :< Init' b as

type family Last' (a :: k) (as :: [k]) :: k where
  Last' a Ø         = a
  Last' a (b :< as) = Last' b as

-- | Takes a type-level list of 'Constraint's to a single
-- 'Constraint', where @ListC cs@ holds iff all elements
-- of @cs@ hold.
type family ListC (cs :: [Constraint]) :: Constraint where
  ListC  Ø        = ØC
  ListC (c :< cs) = (c, ListC cs)

-- | Map an @(f :: k -> l)@ over a type-level list @(as :: [k])@,
-- giving a list @(bs :: [l])@.
type family (f :: k -> l) <$> (a :: [k]) :: [l] where
  f <$> Ø         = Ø
  f <$> (a :< as) = f a :< (f <$> as)
infixr 4 <$>

-- | Map a list of @(fs :: [k -> l])@ over a single @(a :: k)@,
-- giving a list @(bs :: [l])@.
type family (f :: [k -> l]) <&> (a :: k) :: [l] where
  Ø         <&> a = Ø
  (f :< fs) <&> a = f a :< (fs <&> a)
infixl 5 <&>

type family (f :: [k -> l]) <*> (a :: [k]) :: [l] where
  fs <*> Ø         = Ø
  fs <*> (a :< as) = (fs <&> a) ++ (fs <*> as)
infixr 4 <*>

type instance Mempty = Ø
type instance a <> b = a ++ b

