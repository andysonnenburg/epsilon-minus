{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NoImplicitPrelude #-}
module Path
       ( Path
       , cons
       , nil
       , fromList
       , uncons
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

-- $setup
-- >>> import qualified Data.List as List
-- >>> import Data.String
-- >>> import qualified Path
-- >>> import Test.QuickCheck
-- >>> let uncons (x:xs) = Just (x, xs); uncons [] = Nothing

data Path a
  = Cons {-# UNPACK #-} !Int (Tree a) (Path a)
  | Nil deriving Eq

instance Show a => Show (Path a) where
  showsPrec p xs =
    showParen (p > 10) $ showString "Path.fromList " . shows (toList xs)

instance Functor Path where
  fmap f = \ case
    Cons n_t t xs -> Cons n_t (fmap f t) (fmap f xs)
    Nil -> Nil

-- $foldable
-- prop> null (xs :: String) == null (Path.fromList xs)
-- prop> length (xs :: String) == length (Path.fromList xs)

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
  | Leaf a deriving Eq

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
-- prop> (x:xs :: String) == toList (Path.cons x (Path.fromList xs))
-- prop> Path.fromList (x:xs :: String) == Path.cons x (Path.fromList xs)
cons :: a -> Path a -> Path a
cons x xs = case xs of
  Cons n_t1 t1 (Cons n_t2 t2 ys)
    | n_t1 == n_t2 -> Cons (n_t1 + n_t2 + 1) (Branch x t1 t2) ys
  _ -> Cons 1 (Leaf x) xs

-- |
-- prop> [] == toList Path.nil
-- prop> Path.fromList [] == Path.nil
nil :: Path a
nil = Nil

-- |
-- prop> (xs :: String) == toList (Path.fromList xs)
fromList :: [a] -> Path a
fromList = foldr Path.cons Path.nil

-- |
-- prop> uncons (xs :: String) == (fmap.fmap) toList (Path.uncons (Path.fromList xs))
uncons :: Path a -> Maybe (a, Path a)
uncons = \ case
  Cons n_t (Branch x t1 t2) xs -> Just (x, consTrees (n_t `div` 2) t1 t2 xs)
  Cons _ (Leaf x) xs -> Just (x, xs)
  Nil -> Nothing

-- |
-- prop> List.drop n (xs :: String) == toList (Path.drop n (Path.fromList xs))
drop :: Int -> Path a -> Path a
drop i xs = i `seq` case xs of
  Cons n_t t ys
    | i >= 1 -> case compare i n_t of
      LT -> dropTree i n_t t ys
      EQ -> ys
      GT -> drop (i - n_t) ys
  _ -> xs

dropTree :: Int -> Int -> Tree a -> Path a -> Path a
dropTree i n_t (Branch _ t1 t2) xs
  | i == 1 = consTrees n_t' t1 t2 xs
  | otherwise = case compare i (n_t' + 1) of
    LT -> dropTree (i - 1) n_t' t1 (Cons n_t' t2 xs)
    EQ -> Cons n_t' t2 xs
    GT -> dropTree (i - n_t' - 1) n_t' t2 xs
  where
    n_t' = n_t `div` 2
dropTree _ _ _ xs = xs

consTrees :: Int -> Tree a -> Tree a -> Path a -> Path a
consTrees n_t t1 t2 xs = Cons n_t t1 (Cons n_t t2 xs)

lca :: Eq a => Path a -> Path a -> Path a
lca xs ys = runIdentity $ mlca (\ x y -> Identity $ x == y) xs ys

mlca :: (a -> b -> m Bool) -> Path a -> Path b -> m (Path a)
mlca = undefined
