{-# LANGUAGE FunctionalDependencies #-}
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

module Data.Type.Index.Trans
  ( module Data.Type.Index.Trans
  , (:~:)(..)
  ) where

import Type.Class.Witness ((:~:)(..))
import Type.Family.List
import Type.Family.Tuple

type IxList' = IxList (:~:)
type IxEnv   = IxList (IxFirst (:~:))

class IxLift (t :: (k -> m -> *) -> l -> m -> *) (x :: l) where
  type LiftI t x :: k
  ixLift :: i (LiftI t x) y
         -> t i x y

data IxList (i :: k -> l -> *) :: [k] -> l -> * where
  IxHead :: !(i a b)
         -> IxList i (a :< as) b
  IxTail :: !(IxList i as b)
         -> IxList i (a :< as) b

data IxFirst (i :: k -> l -> *) :: (k,m) -> l -> * where
  IxFirst :: !(i a b)
          -> IxFirst i '(a,c) b

instance (p ~ '(Fst p,Snd p)) => IxLift IxFirst p where
  type LiftI IxFirst p = Fst p
  ixLift = IxFirst

data IxSecond (i :: k -> l -> *) :: (m,k) -> l -> * where
  IxSecond :: !(i a b)
           -> IxSecond i '(c,a) b

instance (p ~ '(Fst p,Snd p)) => IxLift IxSecond p where
  type LiftI IxSecond p = Snd p
  ixLift = IxSecond

data IxOr (i :: k -> m -> *) (j :: l -> m -> *) :: Either k l -> m -> * where
  IxOrL :: !(i a b)
        -> IxOr i j (Left a) b
  IxOrR :: !(j a b)
        -> IxOr i j (Right a) b

instance IxLift (IxOr i) (Right a) where
  type LiftI (IxOr i) (Right a) = a
  ixLift = IxOrR

data IxJust (i :: k -> l -> *) :: Maybe k -> l -> * where
  IxJust :: !(i a b)
         -> IxJust i (Just a) b

data IxComp (i :: k -> l -> *) (j :: l -> m -> *) :: k -> m -> * where
  IxComp :: !(i a b)
         -> !(j b c)
         -> IxComp i j a c

