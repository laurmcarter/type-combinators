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

module Data.Type.Eff.Reader where

import Data.Type.Eff
import Data.Type.Index
import Data.Type.Sum
import Data.Type.MQueue
import Type.Family.List

data Reader e v where
  Reader :: Reader e e

ask :: (Reader e ∈ r) => Eff r e
ask = send Reader

runReader' :: Eff (Reader e :< r) w -> e -> Eff r w
runReader' m e = loop m
  where
  loop = \case
    Val x -> return x
    E u q -> case decompF u of
      Left Reader -> loop $ qApp q e
      Right u     -> E u $ tsingleton $ qComp q loop

runReader :: Eff (Reader e :< r) w -> e -> Eff r w
runReader m e = handleRelay return (\Reader k -> k e) m

local :: forall e a r. (Reader e ∈ r)
  => (e -> e) -> Eff r a -> Eff r a
local f m = do
  e0 <- ask
  let e = f e0
  let h :: Reader e v -> Arr r v a -> Eff r a
      h Reader g = g e
  interpose return h m

