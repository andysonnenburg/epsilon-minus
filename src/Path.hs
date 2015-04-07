{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NoImplicitPrelude #-}
module Path
       ( Path
       , cons
       , nil
       , fromList
       , uncons
       , length
       , drop
       , lca
       , mlca
       ) where

import Data.Bool
import Data.Eq
import Data.Foldable
import Data.Function
import Data.Functor
import Data.Functor.Identity
import Data.Maybe (Maybe (..))
import Data.Monoid
import Data.Ord
import Prelude (Num (..), Int, div, seq, undefined)
import Text.Show

data Path a
  = Cons {-# UNPACK #-} !Int (Tree a) (Path a)
  | Nil

instance Show a => Show (Path a) where
  showsPrec p xs =
    showParen (p > 10) $ showString "Path.fromList " . shows (toList xs)

instance Functor Path where
  fmap f = \ case
    Cons n_t t xs -> Cons n_t (fmap f t) (fmap f xs)
    Nil -> Nil

instance Foldable Path where
  foldMap f = \ case
    Cons _ t xs -> foldMap f t <> foldMap f xs
    Nil -> mempty
  null = \ case
    Nil -> True
    _ -> False
  length = \ case
    Cons n_t _ xs -> n_t + length xs
    Nil -> 0

data Tree a
  = Branch a (Tree a) (Tree a)
  | Leaf a

instance Functor Tree where
  fmap f = \ case
    Branch x t1 t2 -> Branch (f x) (fmap f t1) (fmap f t2)
    Leaf x -> Leaf (f x)

instance Foldable Tree where
  foldMap f = \ case
    Branch x t1 t2 -> f x <> foldMap f t1 <> foldMap f t2
    Leaf x -> f x
  null =
    const False

-- |
-- >>> null (Path.fromList "a")
-- False
-- >>> null (Path.fromList "ab")
-- False
-- >>> null (Path.fromList "abc")
-- False
cons :: a -> Path a -> Path a
cons x xs = case xs of
  Cons n_t1 t1 (Cons n_t2 t2 ys)
    | n_t1 == n_t2 -> Cons (n_t1 + n_t2 + 1) (Branch x t1 t2) ys
  _ -> Cons 1 (Leaf x) xs

-- |
-- >>> null (Path.fromList "")
-- True
nil :: Path a
nil = Nil

-- |
-- >>> Path.fromList "abc"
-- Path.fromList "abc"
fromList :: [a] -> Path a
fromList = foldr Path.cons Path.nil

-- |
-- >>> Path.uncons (Path.fromList "a")
-- Just ('a',Path.fromList "")
-- >>> Path.uncons (Path.fromList "ab")
-- Just ('a',Path.fromList "b")
-- >>> Path.uncons (Path.fromList "abc")
-- Just ('a',Path.fromList "bc")
-- >>> Path.uncons Path.nil
-- Nothing
uncons :: Path a -> Maybe (a, Path a)
uncons = \ case
  Cons n_t t xs -> case t of
    Leaf x -> Just (x, xs)
    Branch x t1 t2 -> case n_t `div` 2 of
      n_t' -> Just (x, Cons n_t' t1 (Cons n_t' t2 xs))
  Nil -> Nothing

-- |
-- >>> Path.drop 0 (Path.fromList "a")
-- Path.fromList "a"
-- >>> Path.drop 1 (Path.fromList "a")
-- Path.fromList ""
-- >>> Path.drop 2 (Path.fromList "a")
-- Path.fromList ""
-- >>> Path.drop 0 (Path.fromList "ab")
-- Path.fromList "ab"
-- >>> Path.drop 1 (Path.fromList "ab")
-- Path.fromList "b"
-- >>> Path.drop 2 (Path.fromList "ab")
-- Path.fromList ""
-- >>> Path.drop 3 (Path.fromList "ab")
-- Path.fromList ""
-- >>> Path.drop 0 (Path.fromList "abc")
-- Path.fromList "abc"
-- >>> Path.drop 1 (Path.fromList "abc")
-- Path.fromList "bc"
-- >>> Path.drop 2 (Path.fromList "abc")
-- Path.fromList "c"
-- >>> Path.drop 3 (Path.fromList "abc")
-- Path.fromList ""
-- >>> Path.drop 4 (Path.fromList "abc")
-- Path.fromList ""
drop :: Int -> Path a -> Path a
drop i xs = i `seq` case xs of
  Cons n_t t ys
    | i <= 0 -> xs
    | otherwise -> case compare i n_t of
      LT -> dropTree i n_t t ys
      EQ -> ys
      GT -> drop (i - n_t) ys
  Nil -> xs

dropTree :: Int -> Int -> Tree a -> Path a -> Path a
dropTree i n_t (Branch _ t1 t2) xs = case compare i (n_t' + 1) of
  LT -> dropTree i n_t' t1 (Cons n_t' t2 xs)
  EQ -> Cons n_t' t2 xs
  GT -> dropTree i n_t' t2 xs
  where
    n_t' = n_t `div` 2
dropTree _ n_t t xs = Cons n_t t xs

lca :: Eq a => Path a -> Path a -> Path a
lca xs ys = runIdentity $ mlca (\ x y -> Identity $ x == y) xs ys

mlca :: (a -> b -> m Bool) -> Path a -> Path b -> m (Path a)
mlca = undefined
