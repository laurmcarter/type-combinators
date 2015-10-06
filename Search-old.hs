{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}

module Search where

import Control.Applicative
import Control.Monad

class Computation c where
  yield :: a -> c a

class Nondet n where
  failure :: n a
  choice  :: n a -> n a -> n a

newtype CPS c a = CPS
  { (>>-) :: forall b. (a -> c b) -> c b
  }
infixl 1 >>-

runCPS :: Computation c => CPS c a -> c a
runCPS a = a >>- yield

instance Functor (CPS c) where
  fmap = liftM

instance Applicative (CPS c) where
  pure  = return
  (<*>) = ap

instance Monad (CPS c) where
  return a = CPS $ \k -> k a
  m >>= f  = CPS $ \k -> m >>- \a -> f a >>- k

instance Nondet n => Alternative (CPS n) where
  empty   = CPS $ \_ -> failure
  a <|> b = CPS $ \k -> choice (a >>- k) (b >>- k)

instance Nondet n => MonadPlus (CPS n)

newtype DiffList a = DiffList
  { (++>) :: [a] -> [a]
  }
infixr 5 ++>

instance Computation DiffList where
  yield a = DiffList (a:)

instance Nondet DiffList where
  failure      = DiffList id
  choice as bs = DiffList $ (as ++>) . (bs ++>)

toList :: DiffList a -> [a]
toList = (++> [])

backtrack :: CPS DiffList a -> [a]
backtrack = toList . runCPS

anyOf :: MonadPlus m => [a] -> m a
anyOf = \case
  a:as -> anyOf as `mplus` return a
  _    -> mzero

-- BFS {{{

newtype Levels n a = Levels
  { levels :: [n a]
  }

instance Computation n => Computation (Levels n) where
  yield a = Levels [yield a]

instance Nondet n => Nondet (Levels n) where
  failure    = Levels []
  choice a b = Levels $ failure : merge (levels a) (levels b)

merge :: Nondet n => [n a] -> [n a] -> [n a]
merge = \case
  []       -> id
  a@(x:xs) -> \case
    []     -> a
    (y:ys) -> choice x y : merge xs ys

runLevels :: Nondet n => Levels n a -> n a
runLevels = foldr choice failure . levels

levelSearch :: CPS (Levels DiffList) a -> [a]
levelSearch = toList . runLevels . runCPS

testBFS :: Show a => (forall m. MonadPlus m => m a) -> IO ()
testBFS m = mapM_ print $ levelSearch m

-- }}}

-- DFS {{{

newtype Bound n a = Bound
  { (!) :: Int -> n a
  }

instance Nondet n => Nondet (Bound n) where
  failure    = Bound $ \_ -> failure
  choice a b = Bound $ \d -> if d == 0
    then failure
    else choice (a ! (d-1)) (b ! (d-1))

levelIter :: (Computation n, Nondet n)
  => Int -> CPS (Bound n) a -> Levels n a
levelIter step a = Levels
  [ (a >>- yieldB) ! d
  | d <- [0,step ..]
  ]
  where
  yieldB x = Bound $ \d -> if d < step
    then yield x
    else failure

iterDepth :: (Computation n, Nondet n) => Int -> CPS (Bound n) a -> n a
iterDepth step = foldr choice failure . levels . levelIter step

-- }}}

test1 :: MonadPlus m => m (Int,Int)
test1 = do
  x <- anyOf [1..5]
  y <- anyOf [6..10]
  return (x,y)

