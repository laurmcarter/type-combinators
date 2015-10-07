{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.Type.Graph where

import Data.Type.Combinator (getI)
import Data.Type.Fin
import Data.Type.Vector
import Type.Family.Nat

import Control.Arrow (second)
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S
import Data.Monoid
import qualified Data.Foldable as F
import Control.Monad (guard)
import Data.Maybe (mapMaybe,fromMaybe,maybeToList)

-- Graph {{{

data Graph n a = Graph
  { gVertices :: V n a
  , gEdges    :: Edges (Fin n)
  }

instance Functor (Graph n) where
  fmap = onVertices . fmap

instance Foldable (Graph n) where
  foldMap f = foldMap f . gVertices

instance Traversable (Graph n) where
  traverse f (Graph vs es) = Graph <$> traverse f vs <*> pure es

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

gFoldMap :: Monoid m => (a -> m) -> (a -> a -> m) -> Graph n a -> m
gFoldMap v e (Graph vs es) = foldMap v vs <> nFoldMap goE es
  where
  goE x y = e (getI $ index x vs) (getI $ index y vs)

gTranspose :: Graph n a -> Graph n a
gTranspose = onEdges nTranspose

gInsVert :: a -> Graph n a -> Graph (S n) a
gInsVert v (Graph vs es) = Graph (v :+ vs) $ nMap FS FS es

gDelVert :: Fin n -> Graph n a -> Graph (Pred n) a
gDelVert n (Graph vs es) = Graph (vDel n vs) $ nMapMaybe (without n) (without n) es

gInsEdge :: Fin n -> Fin n -> Graph n a -> Graph n a
gInsEdge x y = onEdges $ nInsert x y

gDelEdge :: Fin n -> Fin n -> Graph n a -> Graph n a
gDelEdge x y = onEdges $ nDelCod x y

-- }}}

-- Neighbors {{{

newtype Neighbors a b = Neighbors
  { neighborMap :: Map a (Set b)
  } deriving (Eq,Ord,Show)

instance (Ord a, Ord b) => Monoid (Neighbors a b) where
  mempty      = Neighbors M.empty
  mappend a b = Neighbors $ neighborMap a `munion` neighborMap b

nDom :: Ord a => Neighbors a b -> Set a
nDom = S.fromList . M.keys . neighborMap

nCod :: Ord b => Neighbors a b -> Set b
nCod = foldMap id . neighborMap

nEdges :: forall a b. (Ord a, Ord b) => Neighbors a b -> Set (a,b)
nEdges = S.fromList . go . M.assocs . neighborMap
  where
  go :: [(a,Set b)] -> [(a,b)]
  go ps =
    [ (a,b)
    | (a,bs) <- ps
    , b <- S.toList bs
    ]

nFoldMap :: forall a b m. Monoid m => (a -> b -> m) -> Neighbors a b -> m
nFoldMap f = M.foldMapWithKey (foldMap . f) . neighborMap

neighbors :: Ord a => a -> Neighbors a b -> Set b
neighbors a = fromMaybe S.empty . M.lookup a . neighborMap

nVertex :: a -> Neighbors a b
nVertex a = Neighbors $ M.singleton a S.empty

nEdge :: a -> b -> Neighbors a b
nEdge a b = Neighbors $ M.singleton a $ S.singleton b

nFromEdgesVerts :: (Ord a, Ord b) => [(a,b)] -> [a] -> Neighbors a b
nFromEdgesVerts ps as = Neighbors $ M.fromList $
  [ (a,bs)
  | a <- map fst ps
  , let bs = S.fromList
           $ mapFilter
           ( \(a',b) -> b <$ guard (a == a')
           ) ps
  ] ++
  [ (a,S.empty) | a <- as ]

nFromEdges :: (Ord a, Ord b) => [(a,b)] -> Neighbors a b
nFromEdges ps = nFromEdgesVerts ps []

nFromEdgeLists :: (Ord a, Ord b) => [(a,[b])] -> Neighbors a b
nFromEdgeLists = Neighbors . M.fromList . map (second S.fromList)

nTranspose :: (Ord a, Ord b) => Neighbors a b -> Neighbors b a
nTranspose = onNeighbors $ onAssocs go
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
onNeighbors f = Neighbors . f . neighborMap

onAssocs :: Ord c => ([(a,b)] -> [(c,d)]) -> Map a b -> Map c d
onAssocs f = M.fromList . f . M.assocs

{-
nDepthFirst :: forall f a b. (Applicative f, Ord a, Ord b) => (a -> f b) -> Neighbors a a -> f (Neighbors b b)
nDepthFirst f = fmap Neighbors . flip go id . neighborMap
  where
  go :: Map a (Set a) -> (Either f (Map b (Set b)) -> r) -> r
  go m k = case M.minViewWithKey m of
    Nothing          -> k $ pure M.empty
    Just ((a,as),m') -> _
-}

nMapDom :: Ord b => (a -> b) -> Neighbors a c -> Neighbors b c
nMapDom = onNeighbors . M.mapKeys

nMapCod :: Ord b => (a -> b) -> Neighbors c a -> Neighbors c b
nMapCod = onNeighbors . M.map . S.map

nMapMaybeDom :: Ord b => (a -> Maybe b) -> Neighbors a c -> Neighbors b c
nMapMaybeDom f = onNeighbors $ onAssocs $ mapMaybe $ \(a,c) -> (,) <$> f a <*> pure c

nMapMaybeCod :: forall a b c. (Ord b, Ord c) => (a -> Maybe b) -> Neighbors c a -> Neighbors c b
nMapMaybeCod f = onNeighbors $ onAssocs $ mapMaybe go
  where
  go :: (c,Set a) -> Maybe (c,Set b)
  go (c,as) = (,) c <$> if S.null bs
    then Nothing
    else Just bs
    where
    bs = sMapMaybe f as

nMap :: (Ord c, Ord d) => (a -> c) -> (b -> d) -> Neighbors a b -> Neighbors c d
nMap f g = nMapDom f . nMapCod g
{-# INLINE nMap #-}

nMapMaybe :: (Ord a, Ord c, Ord d) => (a -> Maybe c) -> (b -> Maybe d) -> Neighbors a b -> Neighbors c d
nMapMaybe f g = nMapMaybeDom f . nMapMaybeCod g
{-# INLINE nMapMaybe #-}

neighborhood :: forall a. Ord a => a -> Neighbors a a -> Set a
neighborhood a n = go (S.singleton a) a
  where
  go :: Set a -> a -> Set a
  go acc a = if S.null as
    then acc
    else as `bindSet` go (S.union acc as)
    where
    as = neighbors a n S.\\ acc

{-
nSCC :: forall a. Ord a => Neighbors a a -> Set (Set a)
nSCC n = vs `bindSet` go
  where
  vs = nDom n <> nCod n
  go :: a -> Set (Set a)
  go a = _
    where
    as = neighborhood a n
-}

-- }}}

n0 :: Neighbors Int Int
n0 = nFromEdgesVerts
  [ (0,0)
  , (0,1)
  , (1,0)
  , (1,2)
  ] [2]

n1 :: Neighbors Int Int
n1 = nFromEdgeLists
  [ (0,[0,1])
  , (1,[0,2])
  , (2,[])
  ]

-- Util {{{

($/) :: (a -> b -> c) -> b -> a -> c
(f $/ b) a = f a b
infixl 1 $/
{-# INLINE ($/) #-}

minsert :: (Ord k, Monoid a) => k -> a -> Map k a -> Map k a
minsert = M.insertWith (<>)

munion :: (Ord k, Monoid a) => Map k a -> Map k a -> Map k a
munion = M.unionWith (<>)

sMapMaybe :: Ord b => (a -> Maybe b) -> Set a -> Set b
sMapMaybe f = S.fromList . mapMaybe f . S.toList

bindSet :: (Ord a, Ord b) => Set a -> (a -> Set b) -> Set b
bindSet as f = S.unions $ map f $ S.toList as

mapFilter :: Foldable f => (a -> Maybe b) -> f a -> [b]
mapFilter f = foldMap $ maybeToList . f

(&) :: a -> (a -> b) -> b
a & f = f a
infixl 1 &

-- }}}

