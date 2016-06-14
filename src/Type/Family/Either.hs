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
-- Module      :  Type.Family.Either
-- Copyright   :  Copyright (C) 2015 Kyle Carter
-- License     :  BSD3
--
-- Maintainer  :  Kyle Carter <kylcarte@indiana.edu>
-- Stability   :  experimental
-- Portability :  RankNTypes
--
-- Convenient type families for working with type-level @Either@s.
----------------------------------------------------------------------------

module Type.Family.Either where

import Type.Family.Constraint
import Type.Family.Monoid
import Type.Class.Witness

-- | Take a @Maybe Constraint@ to a @Constraint@.
type family EitherC (ec :: Either k Constraint) :: Constraint where
  EitherC (Left  a) = ØC
  EitherC (Right c) = c

type family IsLeft (a :: Either k l) :: Bool where
  IsLeft (Left  a) = True
  IsLeft (Right b) = False

type family IsRight (a :: Either k l) :: Bool where
  IsRight (Left  a) = False
  IsRight (Right b) = True

leftCong :: (a ~ b) :- (IsLeft a ~ IsLeft b)
leftCong = Sub Wit

rightCong :: (a ~ b) :- (IsRight a ~ IsRight b)
rightCong = Sub Wit

leftNotRight :: (Left a ~ Right b) :- Fail
leftNotRight = leftCong

-- | Map over a type-level @Maybe@.
type family (f :: k -> l) <$> (a :: Either m k) :: Either m l where
  f <$> Left  a = Left a
  f <$> Right b = Right (f b)
infixr 4 <$>

eitherFmapCong :: (f ~ g,a ~ b) :- ((f <$> a) ~ (g <$> b))
eitherFmapCong = Sub Wit

type family (f :: Either m (k -> l)) <&> (a :: k) :: Either m l where
  Left  x <&> a = Left x
  Right f <&> a = Right (f a)
infixl 5 <&>

eitherPamfCong :: (f ~ g,a ~ b) :- ((f <&> a) ~ (g <&> b))
eitherPamfCong = Sub Wit

type family (f :: Either m (k -> l)) <*> (a :: Either m k) :: Either m l where
  Left  x <*> Left y  = Left (x <> y)
  Left  x <*> a       = Left x
  f       <*> Left x  = Left x
  Right f <*> Right a = Right (f a)
infixr 4 <*>

eitherApCong :: (f ~ g,a ~ b) :- ((f <*> a) ~ (g <*> b))
eitherApCong = Sub Wit

type family (a :: Either m k) <|> (b :: Either m k) :: Either m k where
  Left  x <|> b = b
  Right a <|> b = Right a
infixr 4 <|>

eitherAltCong :: (a ~ c,b ~ d) :- ((a <|> b) ~ (c <|> d))
eitherAltCong = Sub Wit

type family FromLeft (e :: Either k l) :: k where
  FromLeft (Left a) = a

type family FromRight (e :: Either k l) :: l where
  FromRight (Right b) = b

fromLeftCong :: (a ~ b) :- (FromLeft a ~ FromLeft b)
fromLeftCong = Sub Wit

fromRightCong :: (a ~ b) :- (FromRight a ~ FromRight b)
fromRightCong = Sub Wit

type instance Mempty = Left Mempty
type instance a <> b = a <|> b

