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
-- Module      :  Data.Type.Boolean
-- Copyright   :  Copyright (C) 2015 Kyle Carter
-- License     :  BSD3
--
-- Maintainer  :  Kyle Carter <kylcarte@indiana.edu>
-- Stability   :  experimental
-- Portability :  RankNTypes
--
-- A @singleton@-esque type for type-level Bool values.
--
-----------------------------------------------------------------------------

module Data.Type.Boolean where

import Data.Type.Quantifier (Some(..))
import Type.Family.Bool
import Type.Family.Constraint
import Type.Class.Known
import Type.Class.Higher

data Boolean :: Bool -> * where
  False_ :: Boolean False
  True_  :: Boolean True

deriving instance Eq   (Boolean b)
deriving instance Ord  (Boolean b)
deriving instance Show (Boolean b)

instance Eq1   Boolean
instance Ord1  Boolean
instance Show1 Boolean

instance Read1 Boolean where
  readsPrec1 _ s0 =
    [ (Some True_,s1)
    | ("True_",s1) <- lex s0
    ] ++
    [ (Some False_,s1)
    | ("False_",s1) <- lex s0
    ]

not' :: Boolean a -> Boolean (Not a)
not' = \case
  False_ -> True_
  True_  -> False_

(.||) :: Boolean a -> Boolean b -> Boolean (a || b)
(.||) = \case
  False_ -> id
  True_  -> const True_
infixr 2 .||

(.&&) :: Boolean a -> Boolean b -> Boolean (a && b)
(.&&) = \case
  False_ -> const False_
  True_  -> id
infixr 3 .&&

(.^^) :: Boolean a -> Boolean b -> Boolean (a ^^ b)
a .^^ b = (a .|| b) .&& not' (a .&& b)
infixr 4 .^^

(==>) :: Boolean a -> Boolean b -> Boolean (a ==> b)
a ==> b = not' a .|| b
infixr 1 ==>

(<==>) :: Boolean a -> Boolean b -> Boolean (a <==> b)
(<==>) = (.==)
infixr 1 <==>

class BoolEquality (f :: k -> *) where
  type BoolEqC f (a :: k) (b :: k) :: Constraint
  type BoolEqC f a b = ØC
  (.==) :: BoolEqC f a b => f a -> f b -> Boolean (a == b)
infix 4 .==

instance BoolEquality Boolean where
  (.==) = \case
    False_ -> \case
      False_ -> True_
      True_  -> False_
    True_  -> \case
      False_ -> False_
      True_  -> True_

instance Known Boolean True where
  known = True_

instance Known Boolean False where
  known = False_

