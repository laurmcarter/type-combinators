{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GADTs #-}

module Test where

import Data.Type.Product

import Data.Type.Index
import Data.Type.Index.Quote
import Type.Family.List

import Data.Type.Nat
import Data.Type.Nat.Quote

import Data.Type.Sym
import Data.Type.Sym.Quote

foo :: Index (a :< b :< as) x -> Index (b :< a :< c :< as) x
foo = \case
  [ix|0|]   -> [ix|1|]
  [ix|1|]   -> [ix|0|]
  [ix|i+2|] -> [ix|i+3|]

bar :: Nat x -> Nat [n|x+3|]
bar x = [n|x+3|]

baz :: Prod Nat [ns|1,2,3|]
baz = [ns|1,2,3|]

sA :: [sym|A|]
sA = [sym|A|]

{-
-- quux :: Permutation '[a,b,c] '[c,a,b]
quux = [ixPerm|2 0 1|]
-}

{-
quux :: Permutation '[a,b,c] '[c,a,b]
quux = Perm $ F
      ( _
      )
      ( _
      )
-}


