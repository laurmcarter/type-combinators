{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
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

module Data.Type.Eff where

import Data.Type.Index
import Data.Type.Sum
import Data.Type.MQueue
import Type.Family.List

data Eff r a
  = Val a
  | forall b. E (Sum' r b) (Arrs r b a)

type Arr  r a b = a -> Eff r b
type Arrs r     = MQueue (Eff r)

qApp :: Arrs r a b -> a -> Eff r b
qApp q x = case viewl q of
  V1 k -> k x
  k :| t -> case k x of
    Val y -> qApp t y
    E u q -> E u $ q >< t

qComp :: Arrs r a b -> (Eff r b -> Eff r' c) -> Arr r' a c
qComp g h = h . qApp g

instance Functor (Eff r) where
  fmap f = \case
    Val x -> Val $ f x
    E u q -> E u $ q |> Val . f

instance Applicative (Eff r) where
  pure = Val
  (<*>) = \case
    Val f -> \case
      Val a -> Val $ f a
      E u q -> E u $ q |> Val . f
    E u q -> \case
      Val a -> E u $ q |> Val . ($ a)
      m     -> E u $ q |> (<$> m)

instance Monad (Eff r) where
  m >>= k = case m of
    Val a -> k a
    E u q -> E u $ q |> k

send :: Elem r t => t v -> Eff r v
send t = E (inj' t) $ tsingleton Val

run :: Eff Ø w -> w
run = \case
  Val a -> a
  _     -> error "impossible type"

handleRelay :: (a -> Eff r w)
  -> (forall v. t v -> Arr r v w -> Eff r w)
  -> Eff (t :< r) a -> Eff r w
handleRelay ret h = loop
  where
  loop = \case
    Val x -> ret x
    E u q -> case decomp' u of
      Left  x -> h x k
      Right u -> E u $ tsingleton k
      where
      k = qComp q loop

interpose :: Elem r t => (a -> Eff r w)
  -> (forall v. t v -> Arr r v w -> Eff r w)
  -> Eff r a -> Eff r w
interpose ret h = loop
  where
  loop = \case
    Val x -> ret x
    E u q -> case prj' u of
      Just x -> h x k
      _      -> E u $ tsingleton k
      where
      k = qComp q loop

data Reader e v where
  Reader :: Reader e e

ask :: Elem r (Reader e) => Eff r e
ask = send Reader

runReader' :: Eff (Reader e :< r) w -> e -> Eff r w
runReader' m e = loop m
  where
  loop = \case
    Val x -> return x
    E u q -> case decomp' u of
      Left Reader -> loop $ qApp q e
      Right u     -> E u $ tsingleton $ qComp q loop

runReader :: Eff (Reader e :< r) w -> e -> Eff r w
runReader m e = handleRelay return (\Reader k -> k e) m

local :: forall e a r. Elem r (Reader e)
  => (e -> e) -> Eff r a -> Eff r a
local f m = do
  e0 <- ask
  let e = f e0
  let h :: Reader e v -> Arr r v a -> Eff r a
      h Reader g = g e
  interpose return h m

