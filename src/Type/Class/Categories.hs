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
-- Module      :  Type.Class.Categories
-- Copyright   :  Copyright (C) 2015 Kyle Carter
-- License     :  BSD3
--
-- Maintainer  :  Kyle Carter <kylcarte@indiana.edu>
-- Stability   :  experimental
-- Portability :  RankNTypes
--
-- XXX
--
----------------------------------------------------------------------------

module Type.Class.Categories where

import Type.Class.Witness

import Prelude hiding (id,(.))
import Control.Category
import Control.Arrow hiding ((***))

-- F,Bij {{{

data F p q a b = F
  { fwd :: p a b
  , bwd :: q b a
  }

instance (Category p, Category q) => Category (F p q) where
  id    = F id id
  g . f = F
    { fwd = fwd g . fwd f
    , bwd = bwd f . bwd g
    }

type Partial   = F (Kleisli Maybe) (->)

partial :: (a -> Maybe b) -> (b -> a) -> Partial a b
partial f g = F
  { fwd = Kleisli f
  , bwd = g
  }

(@?) :: Partial a b -> a -> Maybe b
(@?) = runKleisli . fwd
infixl 8 @?

type Bij p = F p p

bij :: p a b -> p b a -> Bij p a b
bij = F

type (<->) = Bij (->)
infixr 5 <->
type (:-:) = Bij (:-)
infixr 4 :-:

(<->) :: p a b -> p b a -> Bij p a b
(<->) = bij

($->) :: Bij p a b -> p a b
($->) = fwd
(<-$) :: Bij p a b -> p b a
(<-$) = bwd
infixr 1 $->, <-$

-- }}}

(<?>) :: r <-> s -> Dec r -> Dec s
(<?>) p = \case
  Proven  a -> Proven  $ p $-> a
  Refuted f -> Refuted $ \a -> f $ p <-$ a
infix 3 <?>

-- Monoidal,Symmetric {{{

class Category c => Monoidal (c :: k -> k -> *) where
  type Tensor c (a :: k) (b :: k) :: k
  type Unit   c :: k
  (.*.) :: c v w -> c x y -> c (Tensor c v x) (Tensor c w y)
  assoc  :: p x -> q y -> r z -> c (Tensor c (Tensor c x y) z) (Tensor c x (Tensor c y z))
  unitL  :: p x -> c (Tensor c (Unit c) x) x
  unitR  :: p x -> c (Tensor c x (Unit c)) x
infixr 3 .*.

class Category c => Symmetric (c :: k -> k -> *) where
  symm :: c a b -> c b a

instance Category p => Symmetric (Bij p) where
  symm p = bwd p <-> fwd p

instance Monoidal (->) where
  type Tensor (->) a b = (a,b)
  type Unit   (->) = ()
  (f .*. g) (a,b) = (f a,g b)
  assoc _ _ _ ((x,y),z) = (x,(y,z))
  unitL _         (_,x) = x
  unitR _         (x,_) = x

instance (Symmetric p, Monoidal p) => Monoidal (Bij p) where
  type Tensor (Bij p) a b = Tensor p a b
  type Unit   (Bij p) = Unit p
  f .*. g = F (fwd f .*. fwd g) (bwd f .*. bwd g)
  assoc x y z = assoc x y z <-> symm (assoc x y z)
  unitL x     = unitL x     <-> symm (unitL x)
  unitR x     = unitR x     <-> symm (unitR x)

-- }}}

