{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
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
-- Module      :  Data.Type.Product.Assoc
-- Copyright   :  Copyright (C) 2015 Kyle Carter
-- License     :  BSD3
--
-- Maintainer  :  Kyle Carter <kylcarte@indiana.edu>
-- Stability   :  experimental
-- Portability :  RankNTypes
--
-- XXX
--
-----------------------------------------------------------------------------

module Data.Type.Product.Assoc where

import Data.Type.Combinator
import Data.Type.Index
import Data.Type.Quantifier
import Type.Class.HFunctor
import Type.Class.Known
import Type.Class.Witness
import Type.Family.Constraint
import Type.Family.List
import Type.Family.Tuple
import Data.Monoid

data Subset (p :: k -> l -> *) :: [k] -> [l] -> * where
  ØS   :: Subset p Ø Ø
  (:+) :: !(p a b)
       -> !(Subset p as bs)
       -> Subset p (a :< as) (b :< bs)
  Skip :: !(Subset p as bs)
       -> Subset p (a :< as) bs
infixr 5 :+

data Assoc (p :: k -> l -> *) :: [k] -> [l] -> * where
  ØA   :: Assoc p Ø Ø
  (:%) :: !(p a b)
       -> !(Assoc p as bs)
       -> Assoc p (a :< as) (b :< bs)
infixr 5 :%

(%:) :: p a b -> p c d -> Assoc p '[a,c] '[b,d]
a %: b = a :% b :% ØA
infixl 6 %:

only :: p a b -> Assoc p '[a] '[b]
only = (:% ØA)

snoc :: Assoc p as bs -> p a b -> Assoc p (as >: a) (bs >: b)
snoc = \case
  ØA      -> only
  b :% as -> (b :%) . (snoc as)

head' :: Assoc p (a :< as) (b :< bs) -> p a b
head' (a :% _) = a

tail' :: Assoc p (a :< as) (b :< bs) -> Assoc p as bs
tail' (_ :% as) = as

-- | Get all but the last element of a non-empty Prod.
init' :: Assoc p (a :< as) (b :< bs) -> Assoc p (Init' a as) (Init' b bs)
init' (a :% as) = case as of
  ØA     -> ØA
  (:%){} -> a :% init' as

-- | Get the last element of a non-empty Prod.
last' :: Assoc p (a :< as) (b :< bs) -> p (Last' a as) (Last' b bs)
last' (a :% as) = case as of
  ØA     -> a
  (:%){} -> last' as

reverse' :: Assoc p as bs -> Assoc p (Reverse as) (Reverse bs)
reverse' = \case
  ØA      -> ØA
  a :% as -> reverse' as `snoc` a

append' :: Assoc p as bs -> Assoc p cs ds -> Assoc p (as ++ cs) (bs ++ ds)
append' = \case
  ØA      -> id
  a :% as -> (a :%) . append' as

indexL :: Index as a -> Assoc p as bs -> Some (p a)
indexL = \case
  IZ   -> \(a :%  _) -> Some a
  IS x -> \(_ :% as) -> indexL x as

indexR :: Index bs b -> Assoc p as bs -> Some (Flip p b)
indexR = \case
  IZ   -> \(a :% _)  -> Some $ Flip a
  IS x -> \(_ :% as) -> indexR x as

index :: Index2 as bs a b -> Assoc p as bs -> p a b
index = \case
  IZ2   -> head'
  IS2 x -> index x . tail'

select :: Assoc (Index2 as bs) cs ds -> Assoc p as bs -> Assoc p cs ds
select = \case
  ØA      -> pure ØA
  x :% xs -> (:%) <$> index x <*> select xs

ix2 :: Index as a -> Index bs b -> Maybe (Index2 as bs a b)
ix2 = \case
  IZ -> \case
    IZ   -> Just IZ2
    IS _ -> Nothing
  IS x -> \case
    IZ   -> Nothing
    IS y -> IS2 <$> ix2 x y

-- map,foldmap,traverse {{{

mapAssoc :: (forall x y. p x y -> q x y) -> Assoc p as bs -> Assoc q as bs
mapAssoc f = \case
  ØA      -> ØA
  a :% as -> f a :% mapAssoc f as

foldMapAssoc :: Monoid m => (forall x y. p x y -> m) -> Assoc p as bs -> m
foldMapAssoc f = \case
  ØA      -> mempty
  a :% as -> f a <> foldMapAssoc f as

traverseAssoc :: Applicative f => (forall x y. p x y -> f (q x y)) -> Assoc p as bs -> f (Assoc q as bs)
traverseAssoc f = \case
  ØA      -> pure ØA
  a :% as -> (:%) <$> f a <*> traverseAssoc f as

imapAssoc :: (forall x y. Index2 as bs x y -> p x y -> q x y) -> Assoc p as bs -> Assoc q as bs
imapAssoc f = \case
  ØA      -> ØA
  a :% as -> f IZ2 a :% imapAssoc (f . IS2) as

ifoldMapAssoc :: Monoid m => (forall x y. Index2 as bs x y -> p x y -> m) -> Assoc p as bs -> m
ifoldMapAssoc f = \case
  ØA      -> mempty
  a :% as -> f IZ2 a <> ifoldMapAssoc (f . IS2) as

itraverseAssoc :: Applicative f => (forall x y. Index2 as bs x y -> p x y -> f (q x y)) -> Assoc p as bs -> f (Assoc q as bs)
itraverseAssoc f = \case
  ØA      -> pure ØA
  a :% as -> (:%) <$> f IZ2 a <*> itraverseAssoc (f . IS2) as

-- }}}

elimAssoc :: q Ø Ø
  -> ( forall x xs y ys.
       Index2 as bs x y
    -> p x y
    -> q xs ys
    -> q (x :< xs) (y :< ys)
     )
  -> Assoc p as bs
  -> q as bs
elimAssoc n c = \case
  ØA      -> n
  a :% as -> c IZ2 a $ elimAssoc n (c . IS2) as

onHead' :: (p a b -> p c d) -> Assoc p (a :< as) (b :< bs) -> Assoc p (c :< as) (d :< bs)
onHead' f (a :% as) = f a :% as

onTail' :: (Assoc p as bs -> Assoc p cs ds) -> Assoc p (a :< as) (b :< bs) -> Assoc p (a :< cs) (b :< ds)
onTail' f (a :% as) = a :% f as

uncurry' :: (p a b -> Assoc p as bs -> r) -> Assoc p (a :< as) (b :< bs) -> r
uncurry' f (a :% as) = f a as

{-
curry' :: (l ~ (a :< as)) => (Prod f l -> r) -> f a -> Prod f as -> r
curry' f a as = f $ a :< as
-}

{-

instance Known (Prod f) Ø where
  known = Ø

instance (Known f a, Known (Prod f) as) => Known (Prod f) (a :< as) where
  type KnownC (Prod f) (a :< as) = (Known f a, Known (Prod f) as)
  known = known :< known

instance Witness ØC ØC (Prod f Ø) where
  r \\ _ = r

instance (Witness p q (f a), Witness s t (Prod f as)) => Witness (p,s) (q,t) (Prod f (a :< as)) where
  type WitnessC (p,s) (q,t) (Prod f (a :< as)) = (Witness p q (f a), Witness s t (Prod f as))
  r \\ (a :< as) = r \\ a \\ as
-}

