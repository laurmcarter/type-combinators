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
-- Module      :  Type.Family.Tuple
-- Copyright   :  Copyright (C) 2015 Kyle Carter
-- License     :  BSD3
--
-- Maintainer  :  Kyle Carter <kylcarte@indiana.edu>
-- Stability   :  experimental
-- Portability :  RankNTypes
--
-- Type-level pairs and triples, along with some convenient aliases and type families
-- over them.
--
-----------------------------------------------------------------------------

module Type.Family.Tuple where

import Type.Family.Monoid
import Type.Class.Witness

type (#) = '(,)
infixr 6 #

-- Fst,Snd,Thd et al {{{

type family Fst (p :: (k,l)) :: k where
  Fst '(a,b) = a

fstCong :: (p ~ q) :- (Fst p ~ Fst q)
fstCong = Sub Wit

type family Snd (p :: (k,l)) :: l where
  Snd '(a,b) = b

sndCong :: (p ~ q) :- (Snd p ~ Snd q)
sndCong = Sub Wit

type family Fst3 (p :: (k,l,m)) :: k where
  Fst3 '(a,b,c) = a

fst3Cong :: (p ~ q) :- (Fst3 p ~ Fst3 q)
fst3Cong = Sub Wit

type family Snd3 (p :: (k,l,m)) :: l where
  Snd3 '(a,b,c) = b

snd3Cong :: (p ~ q) :- (Snd3 p ~ Snd3 q)
snd3Cong = Sub Wit

type family Thd3 (p :: (k,l,m)) :: m where
  Thd3 '(a,b,c) = c

thd3Cong :: (p ~ q) :- (Thd3 p ~ Thd3 q)
thd3Cong = Sub Wit

-- }}}

-- Map et al {{{

type family (f :: k -> l) <$> (a :: (m,k)) :: (m,l) where
  f <$> (a#b) = a # f b
infixr 4 <$>

pairMapCong :: (f ~ g,a ~ b) :- ((f <$> a) ~ (g <$> b))
pairMapCong = Sub Wit

type family (f :: (m,k -> l)) <&> (a :: k) :: (m,l) where
  (r#f) <&> a = r # f a
infixr 4 <&>

type family (f :: (m,k -> l)) <*> (a :: (m,k)) :: (m,l) where
  (r#f) <*> (s#a) = (r <> s) # f a
infixr 4 <*>

-- }}}

-- | A type-level pair is a Monoid over its pairwise components.
type instance Mempty = Mempty # Mempty
type instance (r#a) <> (s#b) = (r <> s) # (a <> b)

type instance Mempty = '(Mempty,Mempty,Mempty)
type instance '(a,b,c) <> '(d,e,f) = '(a<>d,b<>e,c<>f)

