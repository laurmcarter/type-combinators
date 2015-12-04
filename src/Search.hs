{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Search where

import Control.Monad.Trans.Cont
import Control.Monad.Trans.Class
import Control.Monad.IO.Class
import Data.Sequence (Seq,ViewL(..),ViewR(..))
import qualified Data.Sequence as S
-- import Data.Type.Vector
-- import Data.Type.Quantifier
-- import Type.Family.Nat

data Bin a
  = Empty
  | Branch a (Bin a) (Bin a)
  deriving (Eq,Ord,Show)

instance Functor Bin where
  fmap f = \case
    Empty -> Empty
    Branch a l r -> Branch (f a) (f <$> l) (f <$> r)

leaf :: a -> Bin a
leaf a = Branch a Empty Empty

b0 :: Bin Int
b0 = Branch 1
  ( Branch 2
    ( Branch 3
      ( Branch 4 Empty
        ( leaf 5
        )
      )
      ( Branch 6
        ( leaf 7
        )
        Empty
      )
    )
    Empty
  )
  ( Branch 8
    ( leaf 9
    )
    ( Branch 10 Empty
      ( leaf 11
      )
    )
  )

printBin :: Show a => Bin a -> IO ()
printBin = putStrLn . unlines . draw . fmap show

draw :: Bin String -> [String]
draw = \case
  Empty -> ["*"]
  Branch s l r -> s : drawSubs [l,r]
  where
  drawSubs = \case
    []   -> []
    [t]  -> "|" : shift "`- " "   " (draw t)
    t:ts -> "|" : shift "+- " "|  " (draw t) ++ drawSubs ts
  shift first other = zipWith (++) (first : repeat other)

bfn :: Int -> Seq (Bin a) -> Seq (Bin Int)
bfn i s = case S.viewl s of
  EmptyL             -> S.empty
  Empty        :< s' -> Empty S.<| bfn i s'
  Branch _ l r :< s' -> case S.viewr res of
    res' :> r' -> case S.viewr res' of
      res'' :> l' -> Branch i l' r' S.<| res''
      _ -> error "missing 1"
    _ -> error "missing 2"
    where
    res = bfn (i+1) $ s' S.|> l S.|> r

bfnM :: Monad m => (a -> m b) -> Seq (Bin a) -> m (Seq (Bin b))
bfnM f s = case S.viewl s of
  EmptyL             -> return S.empty
  Empty        :< s' -> (Empty S.<|) <$> bfnM f s'
  Branch a l r :< s' -> do
    b <- f a
    res <- bfnM f $ s' S.|> l S.|> r
    case S.viewr res of
      res' :> r' -> case S.viewr res' of
        res'' :> l' -> return $ Branch b l' r' S.<| res''
        _ -> fail "missing 1"
      _ -> fail "missing 2"

(||>) :: Foldable f => Seq a -> f a -> Seq a
(||>) = foldl (S.|>)
infixl 5 ||>

(<||) :: Foldable f => f a -> Seq a -> Seq a
(<||) = flip $ foldr (S.<|)
infixr 5 <||

