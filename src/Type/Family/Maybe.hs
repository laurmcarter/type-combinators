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
-- Module      :  Type.Family.Maybe
-- Copyright   :  Copyright (C) 2015 Kyle Carter
-- License     :  BSD3
--
-- Maintainer  :  Kyle Carter <kylcarte@indiana.edu>
-- Stability   :  experimental
-- Portability :  RankNTypes
--
-- Convenient type families for working with type-level @Maybe@s.
----------------------------------------------------------------------------

module Type.Family.Maybe where

import Type.Family.Constraint
import Type.Family.Monoid
import Type.Class.Witness

-- | Take a @Maybe Constraint@ to a @Constraint@.
type family MaybeC (mc :: Maybe Constraint) :: Constraint where
  MaybeC Nothing  = ØC
  MaybeC (Just c) = c

type family IsNothing (a :: Maybe k) :: Bool where
  IsNothing Nothing  = True
  IsNothing (Just a) = False

nothingCong :: (a ~ b) :- (IsNothing a ~ IsNothing b)
nothingCong = Sub Wit

nothingNotJust :: (Nothing ~ Just a) :- Fail
nothingNotJust = nothingCong

-- | Map over a type-level @Maybe@.
type family (f :: k -> l) <$> (a :: Maybe k) :: Maybe l where
  f <$> Nothing = Nothing
  f <$> Just a  = Just (f a)
infixr 4 <$>

maybeFmapCong :: (f ~ g,a ~ b) :- ((f <$> a) ~ (g <$> b))
maybeFmapCong = Sub Wit

type family (f :: Maybe (k -> l)) <&> (a :: k) :: Maybe l where
  Nothing <&> a = Nothing
  Just f  <&> a = Just (f a)
infixl 5 <&>

maybePamfCong :: (f ~ g,a ~ b) :- ((f <&> a) ~ (g <&> b))
maybePamfCong = Sub Wit

type family (f :: Maybe (k -> l)) <*> (a :: Maybe k) :: Maybe l where
  Nothing <*> a       = Nothing
  f       <*> Nothing = Nothing
  Just f  <*> Just a  = Just (f a)
infixr 4 <*>

maybeApCong :: (f ~ g,a ~ b) :- ((f <*> a) ~ (g <*> b))
maybeApCong = Sub Wit

type family (a :: Maybe k) <|> (b :: Maybe k) :: Maybe k where
  Nothing <|> a       = a
  a       <|> Nothing = a
  Just a  <|> Just b  = Just a
infixr 4 <|>

maybeAltCong :: (a ~ c,b ~ d) :- ((a <|> b) ~ (c <|> d))
maybeAltCong = Sub Wit

type family FromJust (m :: Maybe k) :: k where
  FromJust (Just a) = a

fromJustCong :: (a ~ b) :- (FromJust a ~ FromJust b)
fromJustCong = Sub Wit

type instance Mempty = Nothing
type instance a <> b = a <|> b

