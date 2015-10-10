
module Data.Type.Graph where

import Type.Family.Nat
import Data.Set (Set)
import qualified Data.Set as S
import Control.Applicative hiding ((<**>))
import Control.Monad
import Data.Monoid

data Graph a = Graph
  { adjacent :: (a -> Maybe (Set a)) -> a -> Maybe (Set a)
  }

instance Monoid (Graph a) where
  mempty      = Graph ($)
  mappend a b = Graph $ adjacent a . adjacent b

vertex :: Eq a => a -> Set a -> Graph a
vertex a as = Graph $ replace a $ Just as

vertex_ :: Eq a => a -> Graph a
vertex_ a = vertex a S.empty

{-
(~>) :: Eq a => a -> a -> Graph a
a ~> b = Graph $ update a $ S.insert b
infix 8 ~>
-}

replace :: Eq a => a -> b -> (a -> b) -> a -> b
replace a b k x = if x == a
  then b
  else k x

update :: Eq a => a -> (b -> b) -> (a -> Maybe b) -> a -> Maybe b
update a f k x = if a == x
  then f <$> k x
  else k x

(?) :: a -> a -> Bool -> a
(t ? f) b = if b
  then t
  else f
infix 8 ?

(<$$>) :: (Functor f, Functor g) => (a -> b) -> f (g a) -> f (g b)
(<$$>) = fmap . fmap
infixl 4 <$$>

(<**>) :: (Applicative f, Applicative g) => f (g (a -> b)) -> f (g a) -> f (g b)
(<**>) = liftA2 (<*>)
infixl 4 <**>

puure :: (Applicative f, Applicative g) => a -> f (g a)
puure = pure . pure

