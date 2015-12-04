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
import Type.Family.Tuple hiding (type (<$>),type (<*>),type (<&>))
import Type.Class.Witness

type Ø    = '[]
type (:<) = '(:)
infixr 5 :<

-- | Type-level singleton list.
type Only a = '[a]

-- Null,Append {{{

type family Null (as :: [k]) :: Bool where
  Null Ø         = True
  Null (a :< as) = False

nullCong :: (a ~ b) :- (Null a ~ Null b)
nullCong = Sub Wit

nilNotCons :: (Ø ~ (a :< as)) :- Fail
nilNotCons = nullCong

-- | Appends two type-level lists.
type family (as :: [k]) ++ (bs :: [k]) :: [k] where
  Ø         ++ bs = bs
  (a :< as) ++ bs = a :< (as ++ bs)
infixr 5 ++

appendCong :: (a ~ b,c ~ d) :- ((a ++ c) ~ (b ++ d))
appendCong = Sub Wit

-- }}}

-- Snoc,Reverse {{{

-- | Type-level list snoc.
type family (as :: [k]) >: (a :: k) :: [k] where
  Ø         >: a = Only a
  (b :< as) >: a = b :< (as >: a)
infixl 6 >:

snocCong :: (as ~ bs,a ~ b) :- ((as >: a) ~ (bs >: b))
snocCong = Sub Wit

type family Reverse (as :: [k]) :: [k] where
  Reverse  Ø        = Ø
  Reverse (a :< as) = Reverse as >: a

reverseCong :: (as ~ bs) :- (Reverse as ~ Reverse bs)
reverseCong = Sub Wit

-- }}}

-- Head,Tail,Init,Last {{{

type family Head (as :: [k]) :: k where
  Head (a :< as) = a

type family Tail (as :: [k]) :: [k] where
  Tail (a :< as) = as

type family Init (as :: [k]) :: [k] where
  Init (a :< as) = Init' a as

type family Init' (a :: k) (as :: [k]) :: [k] where
  Init' a Ø = Ø
  Init' a (b :< as) = a :< Init' b as

initCong :: (a ~ b,as ~ bs) :- (Init' a as ~ Init' b bs)
initCong = Sub Wit

type family Last (as :: [k]) :: k where
  Last (a :< as) = Last' a as

type family Last' (a :: k) (as :: [k]) :: k where
  Last' a Ø         = a
  Last' a (b :< as) = Last' b as

lastCong :: (a ~ b,as ~ bs) :- (Last' a as ~ Last' b bs)
lastCong = Sub Wit

-- }}}

-- | Takes a type-level list of 'Constraint's to a single
-- 'Constraint', where @ListC cs@ holds iff all elements
-- of @cs@ hold.
type family ListC (cs :: [Constraint]) :: Constraint where
  ListC  Ø        = ØC
  ListC (c :< cs) = (c, ListC cs)

-- Map et al {{{

-- | Map an @(f :: k -> l)@ over a type-level list @(as :: [k])@,
-- giving a list @(bs :: [l])@.
type family (f :: k -> l) <$> (a :: [k]) :: [l] where
  f <$> Ø         = Ø
  f <$> (a :< as) = f a :< (f <$> as)
infixr 4 <$>

listMapCong :: (f ~ g,as ~ bs) :- ((f <$> as) ~ (g <$> bs))
listMapCong = Sub Wit

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

-- }}}

-- Tuples {{{

type family Fsts (ps :: [(k,l)]) :: [k] where
  Fsts  Ø        = Ø
  Fsts (p :< ps) = Fst p :< Fsts ps

type family Snds (ps :: [(k,l)]) :: [l] where
  Snds  Ø        = Ø
  Snds (p :< ps) = Snd p :< Snds ps

type family Zip (as :: [k]) (bs :: [l]) :: [(k,l)] where
  Zip  Ø         Ø        = Ø
  Zip (a :< as) (b :< bs) = a#b :< Zip as bs

type family Fsts3 (ps :: [(k,l,m)]) :: [k] where
  Fsts3  Ø        = Ø
  Fsts3 (p :< ps) = Fst3 p :< Fsts3 ps

type family Snds3 (ps :: [(k,l,m)]) :: [l] where
  Snds3  Ø        = Ø
  Snds3 (p :< ps) = Snd3 p :< Snds3 ps

type family Thds3 (ps :: [(k,l,m)]) :: [m] where
  Thds3  Ø        = Ø
  Thds3 (p :< ps) = Thd3 p :< Thds3 ps

-- }}}

type instance Mempty = Ø
type instance a <> b = a ++ b

