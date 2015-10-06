{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Search where

import Control.Monad.Trans.Cont
import Control.Monad.Trans.Class
import Control.Monad.IO.Class
import Data.Tree

t0 :: Tree Int
t0 = Node 0
  [ Node 1
    [ Node 4 [ leaf 8 , leaf 9 ]
    , leaf 5
    ]
  , leaf 2
  , Node 3
    [ Node 6 [ leaf 10 ]
    , leaf 7
    ]
  ]

leaf :: a -> Tree a
leaf a = Node a []

{-
bfs :: Tree a -> [a]
bfs tr = go tr id []
  where
  go :: Tree a -> ([a] -> r) -> [a] -> r
  go (Node a ts) k acc = case ts of
    [] -> 
-}

