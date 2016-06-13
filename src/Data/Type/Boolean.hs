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

-- import Data.Type.Quantifier (Some(..))
import Type.Family.Bool
import Type.Class.Known
import Type.Class.Higher
import Type.Class.Witness

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

if' :: Boolean b -> ((b ~ True) => a) -> ((b ~ False) => a) -> a
if' t c a = case t of
  True_  -> c
  False_ -> a

(.?) :: ((b ~ True) => a) -> ((b ~ False) => a) -> Boolean b -> a
(c .? a) t = if' t c a
infix 4 .?

not' :: Boolean a -> Boolean (Not a)
not' = False_ .? True_

(.||) :: Boolean a -> Boolean b -> Boolean (a || b)
(.||) = (True_ .? True_ )
     .? (True_ .? False_)
infixr 2 .||

(.&&) :: Boolean a -> Boolean b -> Boolean (a && b)
(.&&) = (True_  .? False_)
     .? (False_ .? False_)
infixr 3 .&&

(.^^) :: Boolean a -> Boolean b -> Boolean (a ^^ b)
(.^^) = (False_ .? True_ )
     .? (True_  .? False_)
infixr 4 .^^

(==>) :: Boolean a -> Boolean b -> Boolean (a ==> b)
(==>) = (True_ .? False_)
     .? (True_ .? True_ )
infixr 1 ==>

(<==>) :: Boolean a -> Boolean b -> Boolean (a <==> b)
(<==>) = (True_  .? False_)
      .? (False_ .? True_ )
infixr 1 <==>

class BoolEquality (f :: k -> *) where
  boolEquality :: f a -> f b -> Boolean (a == b)

(.==) :: BoolEquality f => f a -> f b -> Boolean (a == b)
(.==) = boolEquality
infix 4 .==

instance BoolEquality Boolean where
  boolEquality = (<==>)

instance TestEquality Boolean where
  testEquality = (qed .? Nothing) .? (Nothing .? qed)

instance Known Boolean True where
  known = True_

instance Known Boolean False where
  known = False_

toBool :: Boolean b -> Bool
toBool = True .? False

