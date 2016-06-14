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
-- Module      :  Data.Type.Length
-- Copyright   :  Copyright (C) 2015 Kyle Carter
-- License     :  BSD3
--
-- Maintainer  :  Kyle Carter <kylcarte@indiana.edu>
-- Stability   :  experimental
-- Portability :  RankNTypes
--
-- A @singleton@-esque type for representing lengths of type-level lists,
-- irrespective of the actual types in that list.
--
-----------------------------------------------------------------------------

module Data.Type.Length where

-- import Data.Type.Quantifier
import Type.Class.Witness
import Type.Class.Higher
import Type.Class.Known
import Type.Family.Constraint
import Type.Family.List
import Type.Family.Nat
import Data.Type.Nat

data Length :: [k] -> * where
  LZ :: Length Ø
  LS :: !(Length as) -> Length (a :< as)

deriving instance Eq   (Length as)
deriving instance Ord  (Length as)
deriving instance Show (Length as)

instance Eq1   Length
instance Ord1  Length
instance Show1 Length

instance Read1 Length where
  readsPrec1 d = readParen (d > 10) $ \s0 ->
    [ (Some LZ,s1)
    | ("LZ",s1) <- lex s0
    ] ++
    [ (l >>- Some . LS,s2)
    | ("LS",s1) <- lex s0
    , (l,s2) <- readsPrec1 11 s1
    ]

instance Known Length Ø where
  known = LZ

instance Known Length as => Known Length (a :< as) where
  type KnownC Length (a :< as) = Known Length as
  known = LS known

instance (n ~ Len as) => Witness ØC (Known Nat n, Known Length as) (Length as) where
  type WitnessC ØC (Known Nat n, Known Length as) (Length as) = (n ~ Len as)
  (\\) r = \case
    LZ -> r
    LS l -> r \\ l

{-
natLen :: Nat (Len as) -> Length as
natLen = \case
  Z_   -> LZ
  S_ n -> _
-}

elimLength :: p Ø
           -> (forall x xs. Length xs -> p xs -> p (x :< xs))
           -> Length as
           -> p as
elimLength z s = \case
  LZ   -> z
  LS l -> s l $ elimLength z s l

lOdd, lEven :: Length as -> Bool
lOdd = \case
  LZ   -> False
  LS l -> lEven l
lEven = \case
  LZ   -> True
  LS l -> lOdd l

