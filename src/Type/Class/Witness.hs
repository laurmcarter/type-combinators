{-# LANGUAGE FlexibleContexts #-}
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
-- Module      :  Type.Class.Witness
-- Copyright   :  Copyright (C) 2015 Kyle Carter
-- License     :  BSD3
--
-- Maintainer  :  Kyle Carter <kylcarte@indiana.edu>
-- Stability   :  experimental
-- Portability :  RankNTypes
--
-- A type @t@ that is a @'Witness' p q t@ provides a 'Constraint' entailment
-- of @q@, given that @p@ holds.
--
-- The 'Witness' class uses an associated 'Constraint' @WitnessC@ to
-- maintain backwards inference of 'Witness' instances with respect
-- to type refinement. See the 'Known' class for more information.
--
-- Heavily inspired by ekmett's constraints library:
-- <http://hackage.haskell.org/package/constraints>
--
-- The code provided here does not /quite/ subsume the @constraints@
-- library, as we do not give classes and instances for representing
-- the standard library's class heirarchy and instance definitions.
----------------------------------------------------------------------------

module Type.Class.Witness
  ( module Type.Class.Witness
  , module Exports
  ) where

import Type.Class.Known
import Type.Family.Constraint

import Data.Type.Equality as Exports
import Data.Void          as Exports

import Prelude hiding (id,(.))
import Control.Category
import Unsafe.Coerce

-- | A reified 'Constraint'.
data Wit :: Constraint -> * where
  Wit :: c => Wit c

data Wit1 :: (k -> Constraint) -> k -> * where
  Wit1 :: c a => Wit1 c a

-- | Reified evidence of 'Constraint' entailment.
--
-- Given a term of @p :- q@, the Constraint @q@ holds
-- if @p@ holds.
--
-- Entailment of 'Constraint's form a 'Category':
--
-- >>> id  :: p :- p
-- >>> (.) :: (q :- r) -> (p :-> q) -> (p :- r)
data (:-) :: Constraint -> Constraint -> * where
  Sub :: { getSub :: p => Wit q } -> p :- q
infixr 4 :-

instance Category (:-) where
  id              = Sub Wit
  Sub bc . Sub ab = Sub $ bc \\ ab

-- | A general eliminator for entailment.
--
-- Given a term of type @t@ with an instance @Witness p q t@
-- and a term of type @r@ that depends on 'Constraint' @q@,
-- we can reduce the Constraint to @p@.
--
-- If @p@ is @ØC@, i.e. the empty 'Constraint' @()@, then
-- a Witness @t@ can completely discharge the Constraint @q@.
class WitnessC p q t => Witness (p :: Constraint) (q :: Constraint) (t :: *) | t -> p q where
  type WitnessC p q t :: Constraint
  type WitnessC p q t = ØC
  (\\) :: p => (q => r) -> t -> r
infixl 1 \\

-- | Convert a 'Witness' to a canonical reified entailment.
entailed :: Witness p q t => t -> p :- q
entailed t = Sub (Wit \\ t)

-- | Convert a 'Witness' to a canonical reified 'Constraint'.
witnessed :: Witness ØC q t => t -> Wit q
witnessed t = Wit \\ t

instance Witness ØC c (Wit c) where
  r \\ Wit = r

-- | An entailment @p :- q@ is a Witness of @q@, given @p@.
instance Witness p q (p :- q) where
  r \\ Sub Wit = r

-- | A type equality @a ':~:' b@ is a Witness that @(a ~ b)@.
instance Witness ØC (a ~ b) (a :~: b) where
  r \\ Refl = r

-- | If the constraint @c@ holds, there is a canonical construction
-- for a term of type @'Wit' c@, viz. the constructor @Wit@.
instance c => Known Wit c where
  type KnownC Wit c = c
  known = Wit

-- | Constraint chaining under @Maybe@.
(/?) :: (Witness p q t, p) => Maybe t -> (q => Maybe r) -> Maybe r
(/?) = \case
  Just t -> (\\ t)
  _      -> \_ -> Nothing
infixr 0 /?

qed :: Maybe (a :~: a)
qed = Just Refl

impossible :: a -> Void
impossible = unsafeCoerce

data Dec a
  = Proven   a
  | Refuted (a -> Void)

class DecEquality (f :: k -> *) where
  decideEquality :: f a -> f b -> Dec (a :~: b)

decCase :: Dec a
  -> (a -> r)
  -> ((a -> Void) -> r)
  -> r
decCase d y n = case d of
  Proven  a -> y a
  Refuted b -> n b

data Bij p a b = Bij
  { fwd :: p a b
  , bwd :: p b a
  }

($->) :: Bij p a b -> p a b
($->) = fwd
(<-$) :: Bij p a b -> p b a
(<-$) = bwd
infixr 1 $->, <-$

instance Category p => Category (Bij p) where
  id    = Bij id id
  g . f = Bij (fwd g . fwd f) (bwd f . bwd g)

class Category c => Monoidal (c :: k -> k -> *) where
  type Tensor c :: k -> k -> k
  type Unit   c :: k
  (.*.) :: c v w -> c x y -> c (Tensor c v x) (Tensor c w y)
  assoc  :: c (Tensor c (Tensor c x y) z) (Tensor c x (Tensor c y z))
  unitL  :: c (Tensor c (Unit c) x) x
  unitR  :: c (Tensor c x (Unit c)) x
infixr 3 .*.

class Category c => Symmetric (c :: k -> k -> *) where
  symm :: c a b -> c b a

instance Category p => Symmetric (Bij p) where
  symm p = bwd p <-> fwd p

instance Monoidal (->) where
  type Tensor (->) = (,)
  type Unit   (->) = ()
  (f .*. g) (a,b) = (f a,g b)
  assoc ((x,y),z) = (x,(y,z))
  unitL (_,x) = x
  unitR (x,_) = x

instance (Symmetric p, Monoidal p) => Monoidal (Bij p) where
  type Tensor (Bij p) = Tensor p
  type Unit   (Bij p) = Unit p
  (.*.) = (***)
  assoc = assoc <-> symm assoc
  unitL = unitL <-> symm unitL
  unitR = unitR <-> symm unitR

(***) :: Monoidal p => Bij p a b -> Bij p c d -> Bij p (Tensor p a c) (Tensor p b d)
f *** g = (fwd f .*. fwd g) <-> (bwd f .*. bwd g)
infixr 3 ***

type (<->) = Bij (->)
infixr 5 <->

(<->) :: p a b -> p b a -> Bij p a b
(<->) = Bij

(<?>) :: r <-> s -> Dec r -> Dec s
(<?>) p = \case
  Proven  a -> Proven  $ p $-> a
  Refuted f -> Refuted $ \a -> f $ p <-$ a
infix 3 <?>

