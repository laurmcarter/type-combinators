{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.Type.Graph where

import Data.Type.Fin
import Data.Type.Vector
import Type.Family.Nat

import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S
import Data.Monoid
import qualified Data.Foldable as F
import Control.Monad (guard)
import Data.Maybe (mapMaybe)

data Graph n a = Graph
  { gVertices :: V n a
  , gEdges    :: Edges (Fin n)
  }

type Edges a = Neighbors a a

onVertices :: (V n a -> V n b) -> Graph n a -> Graph n b
onVertices f (Graph vs es) = Graph (f vs) es

onEdges :: (Edges (Fin n) -> Edges (Fin n)) -> Graph n a -> Graph n a
onEdges f (Graph vs es) = Graph vs (f es)

gEmpty :: Graph Z a
gEmpty = Graph ØV mempty

gVertex :: a -> Graph (S Z) a
gVertex a = Graph (a :+ ØV) mempty

gEdge :: Fin n -> Fin n -> Graph n a -> Graph n a
gEdge x y = onEdges $ nInsert x y

(~>) :: Fin n -> Fin n -> Graph n a -> Graph n a
(~>) = gEdge
infix 8 ~>
{-# INLINE (~>) #-}

(~~) :: Fin n -> Fin n -> Graph n a -> Graph n a
x ~~ y = (x ~> y) . (y ~> x)
infix 8 ~~
{-# INLINE (~~) #-}

gInsVert :: a -> Graph n a -> Graph (S n) a
gInsVert v (Graph vs es) = Graph (v :+ vs) $ nMap FS FS es

gDelEdge :: Fin n -> Fin n -> Graph n a -> Graph n a
gDelEdge x y = onEdges $ nDelCod x y

-- Neighbors {{{

newtype Neighbors a b = Neighbors
  { neighbors :: Map a (Set b)
  } deriving (Eq,Ord,Show)

instance (Ord a, Ord b) => Monoid (Neighbors a b) where
  mempty      = Neighbors M.empty
  mappend a b = Neighbors $ neighbors a `munion` neighbors b

nVertex :: a -> Neighbors a b
nVertex a = Neighbors $ M.singleton a S.empty

nEdge :: a -> b -> Neighbors a b
nEdge a b = Neighbors $ M.singleton a $ S.singleton b

nReverse :: (Ord a, Ord b) => Neighbors a b -> Neighbors b a
nReverse = onNeighbors $ onAssocs go
  where
  go ps = map getRev bs
    where
    bs = F.toList $ S.unions $ map snd ps
    getRev b = (,) b
      $ S.fromList
      $ mapMaybe $/ ps
      $ \(a,bs) -> do
        guard $ S.member b bs
        return a

nInsert :: (Ord a, Ord b) => a -> b -> Neighbors a b -> Neighbors a b
nInsert a b = mappend $ nEdge a b

nDelDom :: Ord a => a -> Neighbors a b -> Neighbors a b
nDelDom = onNeighbors . M.delete

nDelCod :: (Ord a, Ord b) => a -> b -> Neighbors a b -> Neighbors a b
nDelCod a b = onNeighbors $ M.alter (>>= go) a
  where
  go bs = if S.null bs'
    then Nothing
    else Just bs'
    where
    bs' = S.delete b bs

onNeighbors :: (Map a (Set b) -> Map c (Set d)) -> Neighbors a b -> Neighbors c d
onNeighbors f = Neighbors . f . neighbors

onAssocs :: Ord c => ([(a,b)] -> [(c,d)]) -> Map a b -> Map c d
onAssocs f = M.fromList . f . M.assocs

nMapDom :: Ord b => (a -> b) -> Neighbors a c -> Neighbors b c
nMapDom = onNeighbors . M.mapKeys

nMapCod :: Ord b => (a -> b) -> Neighbors c a -> Neighbors c b
nMapCod = onNeighbors . M.map . S.map

nMap :: (Ord c, Ord d) => (a -> c) -> (b -> d) -> Neighbors a b -> Neighbors c d
nMap f g = nMapDom f . nMapCod g
{-# INLINE nMap #-}

-- }}}

-- Util {{{

($/) :: (a -> b -> c) -> b -> a -> c
(f $/ b) a = f a b
infixl 1 $/
{-# INLINE ($/) #-}

minsert :: (Ord k, Monoid a) => k -> a -> Map k a -> Map k a
minsert = M.insertWith (<>)

munion :: (Ord k, Monoid a) => Map k a -> Map k a -> Map k a
munion = M.unionWith (<>)

-- }}}

