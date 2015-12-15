{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
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
import Data.Void          as Exports hiding (absurd)
import qualified Data.Void as Void

import Prelude hiding (id,(.))
import Control.Category
import Control.Arrow
import Unsafe.Coerce

-- Wit {{{

-- | A reified 'Constraint'.
data Wit :: Constraint -> * where
  Wit :: c => Wit c

data Wit1 :: (k -> Constraint) -> k -> * where
  Wit1 :: c a => Wit1 c a

-- }}}

-- (:-) {{{

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

-- }}}

-- Witness {{{

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

(//) :: (Witness p q t, p) => t -> (q => r) -> r
t // r = r \\ t
infixr 0 //

-- | Convert a 'Witness' to a canonical reified 'Constraint'.
witnessed :: Witness ØC q t => t -> Wit q
witnessed t = Wit \\ t

-- | Convert a 'Witness' to a canonical reified entailment.
entailed :: Witness p q t => t -> p :- q
entailed t = Sub (Wit \\ t)

-- }}}

-- Constraint Combinators {{{

class Fails (c :: Constraint) where
  failC :: c :- Fail

absurdC :: Fails a => a :- b
absurdC = contraC failC

class c => Const (c :: Constraint) (d :: k) where
  constC :: Wit c

instance c => Const c d where
  constC = Wit

class f (g a) => (∘) (f :: l -> Constraint) (g :: k -> l) (a :: k) where
  compC :: Wit (f (g a))

instance f (g a) => (f ∘ g) a where
  compC = Wit
infixr 9 ∘

class (f a,g a) => (∧) (f :: k -> Constraint) (g :: k -> Constraint) (a :: k) where
  conjC :: (Wit (f a),Wit (g a))
infixr 7 ∧

instance (f a,g a) => (f ∧ g) a where
  conjC = (Wit,Wit)

class (∨) (f :: k -> Constraint) (g :: k -> Constraint) (a :: k) where
  disjC :: Either (Wit (f a)) (Wit (g a))
infixr 6 ∨

eitherC :: forall f g a b. f a :- b -> g a :- b -> (f ∨ g) a :- b
eitherC f g = Sub $ case ((disjC :: Either (Wit (f a)) (Wit (g a))),f,g) of
  (Left  a,Sub b,_    ) -> b \\ a
  (Right a,_    ,Sub b) -> b \\ a

pureC :: b => a :- b
pureC = Sub Wit

contraC :: a :- Fail -> a :- b
contraC = (bottom .)

-- }}}

-- Forall {{{

class Forall (p :: k -> Constraint) (q :: k -> Constraint) where
  forall :: p a :- q a
  default forall :: q a => p a :- q a
  forall = pureC

-- }}}

-- Initial/Terminal {{{

commute :: (a ~ b) :- (b ~ a)
commute = Sub Wit

type family Holds (b :: Bool) (c :: Constraint) :: Constraint where
  Holds True  c = c
  Holds False c = ØC

falso :: (b ~ False) :- Holds b c
falso = Sub Wit

top :: a :- ØC
top = Sub Wit

type Fail = (True ~ False)

bottom :: Fail :- c
bottom = falso

instance Witness ØC c (Wit c) where
  r \\ Wit = r

instance Witness ØC (c a) (Wit1 c a) where
  r \\ Wit1 = r

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

instance c a => Known (Wit1 c) a where
  type KnownC (Wit1 c) a = c a
  known = Wit1

-- | Constraint chaining under @Maybe@.
(//?) :: (Witness p q t, p) => Maybe t -> (q => Maybe r) -> Maybe r
(//?) = \case
  Just t -> (\\ t)
  _      -> \_ -> Nothing
infixr 0 //?

(//?+) :: (Witness p q t, p) => Either e t -> (q => Either e r) -> Either e r
(//?+) = \case
  Left  e -> \_ -> Left e
  Right t -> (\\ t)
infixr 0 //?+

witMaybe :: (Witness p q t, p) => Maybe t -> (q => Maybe r) -> Maybe r -> Maybe r
witMaybe mt y n = case mt of
  Just t -> y \\ t
  _      -> n

qed :: Maybe (a :~: a)
qed = Just Refl

impossible :: a -> Void
impossible = unsafeCoerce

(=?=) :: TestEquality f => f a -> f b -> Maybe (a :~: b)
(=?=) = testEquality
infix 4 =?=

class TestEquality1 (f :: k -> l -> *) where
  testEquality1 :: f a c -> f b c -> Maybe (a :~: b)

(=??=) :: TestEquality1 f => f a c -> f b c -> Maybe (a :~: b)
(=??=) = testEquality1
infix 4 =??=

-- }}}

-- Dec {{{

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

-- }}}

absurd :: Arrow p => p Void a
absurd = arr Void.absurd

{-
-- Category Classes {{{

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

-- }}}
-}

