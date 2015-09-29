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

type Only a = '[a]

type family (as :: [k]) ++ (bs :: [k]) :: [k] where
  Ø         ++ bs = bs
  (a :< as) ++ bs = a :< (as ++ bs)
infixr 5 ++

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

type family ListC (cs :: [Constraint]) :: Constraint where
  ListC  Ø        = ØC
  ListC (c :< cs) = (c, ListC cs)

type family (f :: k -> l) <$> (a :: [k]) :: [l] where
  f <$> Ø         = Ø
  f <$> (a :< as) = f a :< (f <$> as)
infixr 4 <$>

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

