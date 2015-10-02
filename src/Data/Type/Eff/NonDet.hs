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

module Data.Type.Eff.NonDet where

import Data.Type.Eff
import Data.Type.Eff.Writer
import Data.Type.Index
import Data.Type.Sum
import Data.Type.MQueue
import Type.Family.List

import Control.Applicative
import Control.Monad

data NonDet a where
  MZero :: NonDet a
  MPlus :: NonDet Bool

instance (NonDet ∈ r) => Alternative (Eff r) where
  empty   = send MZero
  a <|> b = send MPlus >>= a ? b

instance (NonDet ∈ r) => MonadPlus (Eff r)

-- mc :: Alternative f => Eff (NonDet :< r) a -> Eff r (f a)
-- mc = handleRelay (return . pure) $ \case
  

makeChoice :: Alternative f => Eff (NonDet :< r) a -> Eff r (f a)
makeChoice = go []
  where
  -- go :: Alternative f => [Eff (NonDet :< r) a] -> Eff (NonDet :< r) a -> Eff r (f a)
  go jq = \case
    Val x -> case jq of
      h:t -> go t h >>= \r -> return (pure x <|> r)
      _   -> return $ pure x
    E u q -> case decompF u of
      Left a -> case a of
        MZero -> case jq of
          h:t -> go t h
          _   -> return empty
        MPlus -> go (qApp q False : jq) (qApp q True)
      Right u -> E u $ tsingleton $ go jq . qApp q

msplit :: (NonDet ∈ r) => Eff r a -> Eff r (Maybe (a,Eff r a))
msplit = go []
  where
  go jq = \case
    Val x -> return $ Just (x,msum jq)
    E u q -> case prjF u of
      Just a -> case a of
        MZero -> case jq of
          h:t -> go t h
          _   -> return Nothing
        MPlus -> go (qApp q False : jq) (qApp q True)
      _ -> E u $ tsingleton $ qComp q $ go jq

(?) :: a -> a -> Bool -> a
t ? f = \case
  True -> t
  _    -> f
infix 4 ?



