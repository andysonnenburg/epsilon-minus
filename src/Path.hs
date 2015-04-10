{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE NoImplicitPrelude #-}
module Path
       ( Path
       , cons
       , fromList
       , uncons
       , drop
       , lca
       , lcaM
       ) where

import Control.Applicative
import Control.Monad
import Data.Bool
import Data.Bits
import Data.Eq
import Data.Foldable
import Data.Function
import Data.Functor.Identity
import Data.Traversable
import Data.Maybe (Maybe (..))
import Data.Monoid
import Data.Ord
import Prelude (Num (..), Int, div, seq, subtract)
import Text.Show

-- $setup
-- >>> import Data.Char
-- >>> import qualified Data.List as List
-- >>> import Data.String
-- >>> import Data.Tuple
-- >>> import qualified Path
-- >>> import Test.QuickCheck
-- >>> let uncons (x:xs) = Just (x, xs); uncons [] = Nothing
-- >>> :{
-- let lca xs ys =
--       fmap fst $
--       List.dropWhile (uncurry (/=)) $
--       List.zip
--       (List.drop (n_xs - n_ys) xs)
--       (List.drop (n_ys - n_xs) ys)
--       where
--         n_xs = length xs
--         n_ys = length ys
-- :}

data Path a
  = Cons {-# UNPACK #-} !Int (Tree a) (Path a)
  | Nil deriving (Eq, Functor, Traversable)

instance Show a => Show (Path a) where
  showsPrec p xs =
    showParen (p > 10) $ showString "Path.fromList " . shows (toList xs)

-- $monoid
-- prop> mempty == toList (mempty :: Path Char)
-- prop> Path.fromList mempty == mempty
-- prop> (xs :: String) <> ys == toList (Path.fromList xs <> Path.fromList ys)

instance Monoid (Path a) where
  mempty = Nil
  mappend = flip (foldr cons)

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
  | Leaf a deriving (Eq, Functor, Traversable)

-- $foldable
-- >>> length (Leaf 'a')
-- 1
-- >>> length (Branch 'a' (Leaf 'b') (Leaf 'c'))
-- 3
-- >>> null (Leaf 'a')
-- False
-- >>> null (Branch 'a' (Leaf 'b') (Leaf 'c'))
-- False

instance Foldable Tree where
  foldMap f = \ case
    Branch x t_1 t_2 -> f x <> foldMap f t_1 <> foldMap f t_2
    Leaf x -> f x
  length = subtract 1 . unsafeShiftL 1 . fix (\ rec' n -> \ case
    Branch _ t_1 _ -> let n' = n + 1 in n' `seq` rec' n' t_1
    Leaf _ -> n) 1
  null =
    const False

-- |
-- prop> (x:xs :: String) == toList (Path.cons x (Path.fromList xs))
-- prop> Path.fromList (x:xs :: String) == Path.cons x (Path.fromList xs)
cons :: a -> Path a -> Path a
cons x xs = case xs of
  Cons n_t_1 t_1 (Cons n_t_2 t_2 ys)
    | n_t_1 == n_t_2 -> Cons (n_t_1 + n_t_2 + 1) (Branch x t_1 t_2) ys
  _ -> Cons 1 (Leaf x) xs

-- |
-- prop> (xs :: String) == toList (Path.fromList xs)
fromList :: [a] -> Path a
fromList = foldr cons mempty

-- |
-- prop> uncons (xs :: String) == (fmap.fmap) toList (Path.uncons (Path.fromList xs))
uncons :: Path a -> Maybe (a, Path a)
uncons = \ case
  Cons n_t (Branch x t_1 t_2) xs -> Just (x, consTrees (n_t `div` 2) t_1 t_2 xs)
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
dropTree i n_t (Branch _ t_1 t_2) xs
  | i == 1 = consTrees n_t' t_1 t_2 xs
  | otherwise = case compare i (n_t' + 1) of
    LT -> dropTree (i - 1) n_t' t_1 (Cons n_t' t_2 xs)
    EQ -> Cons n_t' t_2 xs
    GT -> dropTree (i - n_t' - 1) n_t' t_2 xs
  where
    n_t' = n_t `div` 2
dropTree _ _ _ xs = xs

-- |
-- prop> \ (Ordered xs) (Ordered ys) -> lca (xs :: String) ys == toList (Path.lca (Path.fromList xs) (Path.fromList ys))
lca :: Eq a => Path a -> Path a -> Path a
lca xs ys = runIdentity $ lcaM (\ x y -> Identity $ x == y) xs ys

lcaM :: Monad m => (a -> b -> m Bool) -> Path a -> Path b -> m (Path a)
lcaM f xs ys =
  dropWhileM2 f' (drop (n_xs - n_ys) xs) (drop (n_ys - n_xs) ys)
  where
    f' x y = not <$> f x y
    n_xs = length xs
    n_ys = length ys

dropWhileM2 :: Monad m => (a -> b -> m Bool) -> Path a -> Path b -> m (Path a)
dropWhileM2 f xs@(Cons n_t t_x xs') (Cons _ t_y ys') =
  ifM
  (foldRoot2 f t_x t_y)
  (ifM
   (foldHeadA2 f xs' ys')
   (dropWhileM2 f xs' ys')
   (dropTreeWhileM2 f n_t t_x t_y xs'))
  (pure xs)
dropWhileM2 _ _ _ =
  pure Nil

dropTreeWhileM2 :: Monad m => (a -> b -> m Bool) -> Int -> Tree a -> Tree b -> Path a -> m (Path a)
dropTreeWhileM2 f n_t (Branch _ t_x_1 t_x_2) (Branch _ t_y_1 t_y_2) xs =
  ifM
  (foldRoot2 f t_x_1 t_y_1)
  (ifM
   (foldRoot2 f t_x_2 t_y_2)
   (dropTreeWhileM2 f n_t' t_x_2 t_y_2 xs)
   (dropTreeWhileM2 f n_t' t_x_1 t_y_1 (Cons n_t' t_x_2 xs)))
  (pure $ consTrees n_t' t_x_1 t_x_2 xs)
  where
    n_t' = n_t `div` 2
dropTreeWhileM2 _ _ _ _ xs = pure xs

consTrees :: Int -> Tree a -> Tree a -> Path a -> Path a
consTrees n_t t_1 t_2 xs = Cons n_t t_1 (Cons n_t t_2 xs)

ifM :: Monad m => m Bool -> m a -> m a -> m a
ifM p x y = p >>= bool y x

foldHeadA2 :: Applicative f => (a -> b -> f Bool) -> Path a -> Path b -> f Bool
foldHeadA2 f (Cons _ xs _) (Cons _ ys _) = foldRoot2 f xs ys
foldHeadA2 _ _ _ = pure False

foldRoot2 :: (a -> b -> c) -> Tree a -> Tree b -> c
foldRoot2 f xs ys = f (root xs) (root ys)

root :: Tree a -> a
root (Branch x _ _) = x
root (Leaf x) = x
