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

module Data.Type.Quantifier where

import Data.Type.Combinator

data Some (f :: k -> *) :: * where
  Some :: f a -> Some f

some :: Some f -> (forall a. f a -> r) -> r
some (Some a) f = f a

type Some2 f = Some (Some :.: f)

pattern Some2 :: f a b -> Some2 f
pattern Some2 a = Some (Comp (Some a))

data All (f :: k -> *) :: * where
  All :: { instAll :: forall (a :: k). f a } -> All f

data (f :: k -> *) :-> (g :: k -> *) where
  NT :: (forall a. f a -> g a) -> f :-> g
infixr 4 :->

data (p :: k -> l -> *) :--> (q :: k -> l -> *) where
  NT2 :: (forall a b. p a b -> q a b) -> p :--> q
infixr 4 :-->

