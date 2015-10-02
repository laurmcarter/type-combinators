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

module Data.Type.Eff.Writer where

import Data.Type.Eff
import Data.Type.Index
import Data.Type.Sum
import Data.Type.MQueue
import Type.Family.List
import Control.Arrow

data Writer o v where
  Writer :: ([o] -> [o]) -> Writer o ()

tell :: (Writer o ∈ r) => o -> Eff r ()
tell = send . Writer . (:)

listen :: forall o r a. (Writer o ∈ r) => Eff r a -> Eff r (a,[o])
listen = fmap (second ($[])) . interpose
  ( \a -> return (a,id) )
  (\(Writer f :: Writer o v) k -> k () >>= \(a,g) -> return (a,f . g))

-- censor :: (Writer o ∈ r) => ([o] -> [o]) -> Eff r a -> Eff r a
-- censor 

runWriter :: Eff (Writer o :< r) a -> Eff r (a,[o])
runWriter = handleRelay
  ( \a -> return (a,[]) )
  $ \(Writer f) k -> k () >>= \(a,os) -> return (a,f os)

