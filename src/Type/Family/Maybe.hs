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

module Type.Family.Maybe
  ( module Type.Family.Maybe
  , type (==)
  ) where

import Type.Family.Constraint
import Type.Family.Monoid

import Data.Type.Equality

type family MaybeC (mc :: Maybe Constraint) :: Constraint where
  MaybeC Nothing  = ØC
  MaybeC (Just c) = c

type family (f :: k -> l) <$> (a :: Maybe k) :: Maybe l where
  f <$> Nothing = Nothing
  f <$> Just a  = Just (f a)
infixr 4 <$>

type family (f :: Maybe (k -> l)) <&> (a :: k) :: Maybe l where
  Nothing <&> a = Nothing
  Just f  <&> a = Just (f a)
infixl 5 <&>

type family (f :: Maybe (k -> l)) <*> (a :: Maybe k) :: Maybe l where
  Nothing <*> a       = Nothing
  f       <*> Nothing = Nothing
  Just f  <*> Just a  = Just (f a)
infixr 4 <*>

type family (a :: Maybe k) <|> (b :: Maybe k) :: Maybe k where
  Nothing <|> a       = a
  a       <|> Nothing = a
  Just a  <|> Just b  = Just a
infixr 4 <|>

type family FromJust (m :: Maybe k) :: k where
  FromJust (Just a) = a

type instance Mempty = Nothing
type instance a <> b = a <|> b

