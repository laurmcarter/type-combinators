{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE LambdaCase #-}

module Data.Type.Product.Env where

import Data.Type.Combinator (Comp1(..))
import Data.Type.Conjunction
import Data.Type.Boolean
import Data.Type.Index
import Data.Type.Index.Trans
import Data.Type.Option
import Data.Type.Product
import Type.Class.Higher
import Type.Class.Witness
import Type.Family.Bool
import Type.Family.List

newtype Env k v ps = Env
  { getEnv :: Prod (k :*: v) ps
  }

type family Member (x :: k) (ps :: [(k,v)]) :: Bool where
  Member x Ø              = False
  Member x ('(y,a) :< ps) = (x == y) || Member x ps

member' :: BoolEquality k => k x -> Env k v ps -> Boolean (Member x ps)
member' x = (. getEnv) $ \case
  Ø               -> False_
  (y :*: _) :< ps -> (x .== y) .|| member' x (Env ps)

type family Lookup (x :: k) (ps :: [(k,v)]) :: Maybe v where
  Lookup x Ø              = Nothing
  Lookup x ('(y,a) :< ps) = If (x == y) (Just a) (Lookup x ps)

lookup' :: BoolEquality k => k x -> Env k v ps -> Option v (Lookup x ps)
lookup' x = (. getEnv) $ \case
  Ø              -> Nothing_
  (y :*: a) :< ps -> if' (x .== y)
    (Just_ a)
    (lookup' x $ Env ps)

type family Insert (x :: k) (a :: v) (ps :: [(k,v)]) :: [(k,v)] where
  Insert x a Ø              = '[ '(x,a) ]
  Insert x a ('(y,b) :< ps) = If (x == y) ('(x,a) :< ps) ('(y,b) :< Insert x a ps)

insert' :: BoolEquality k => k x -> v a -> Env k v ps -> Env k v (Insert x a ps)
insert' x a = (. getEnv) $ \case
  Ø               -> Env $ (x :*: a) :< Ø
  (y :*: b) :< ps -> if' (x .== y)
    (Env $ (x :*: a) :< ps)
    (Env $ (y :*: b) :< getEnv (insert' x a (Env ps)))

type family Delete (x :: k) (ps :: [(k,v)]) :: [(k,v)] where
  Delete x Ø              = Ø
  Delete x ('(y,a) :< ps) = If (x == y) ps ('(y,a) :< Delete x ps)

delete' :: BoolEquality k => k x -> Env k v ps -> Env k v (Delete x ps)
delete' x = (. getEnv) $ \case
  Ø               -> Env Ø
  (y :*: a) :< ps -> if' (x .== y)
    (Env ps)
    (Env $ (y :*: a) :< getEnv (delete' x (Env ps)))

type family Difference (ps :: [(k,v)]) (qs :: [(k,w)]) :: [(k,v)] where
  Difference ps Ø              = ps
  Difference ps ('(x,a) :< qs) = Delete x (Difference ps qs)

difference' :: BoolEquality k => Env k v ps -> Env k w qs -> Env k v (Difference ps qs)
difference' ps = (. getEnv) $ \case
  Ø               -> ps
  (x :*: _) :< qs -> delete' x $ difference' ps (Env qs)

(.\\) :: BoolEquality k => Env k v ps -> Env k w qs -> Env k v (Difference ps qs)
(.\\) = difference'

type family Union (ps :: [(k,v)]) (qs :: [(k,v)]) :: [(k,v)] where
  Union ps Ø              = ps
  Union ps ('(x,a) :< qs) = Insert x a (Union ps qs)

union' :: BoolEquality k => Env k v ps -> Env k v qs -> Env k v (Union ps qs)
union' ps = (. getEnv) $ \case
  Ø               -> ps
  (x :*: a) :< qs -> insert' x a $ union' ps (Env qs)

type family Intersection (ps :: [(k,v)]) (qs :: [(k,w)]) :: [(k,v)] where
  Intersection Ø              qs = Ø
  Intersection ('(x,a) :< ps) qs = If (Member x qs) ('(x,a) :< Intersection ps qs) (Intersection ps qs)

intersection' :: BoolEquality k => Env k v ps -> Env k w qs -> Env k v (Intersection ps qs)
intersection' ps qs = case getEnv ps of
  Ø                -> Env Ø
  (x :*: a) :< ps' -> if' (member' x qs) (Env $ (x :*: a) :< getEnv rest) rest
    where
    rest = intersection' (Env ps') qs

instance Functor1 (Env k) where
  map1 f = Env . getComp1 . map1 f . Comp1 . getEnv

instance IxFunctor1 (IxList (IxSecond (:~:))) (Env k) where
  imap1 f = Env . imap1 (\i -> imap1 $ \j -> f $ ixList i j) . getEnv

ixList :: Index as a -> i a b -> IxList i as b
ixList = \case
  IZ   -> IxHead
  IS x -> IxTail . ixList x

