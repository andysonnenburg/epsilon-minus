{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NoImplicitPrelude #-}
module UnionFind
       ( Ref
       , new
       , read
       , write
       , modify
       , union
       ) where

import Control.Applicative
import Control.Category
import Control.Monad
import Control.Monad.ST
import Data.Coerce
import Data.Function (($), fix, flip)
import Data.Ord
import Data.Word
import Lens
import Prelude (($!), (/=), minBound)
import qualified ST

-- $setup
-- >>> import Prelude (succ)

newtype Ref s a = Ref (ST.Ref s (Value s a))

data Value s a
  = Repr {-# UNPACK #-} !(Ranked a)
  | Link {-# UNPACK #-} !(ST.Ref s (Value s a))

data Ranked a = Ranked {-# UNPACK #-} !Rank a deriving Functor

rank :: Functor f => Lens' f (Ranked a) Rank
rank =
  lens
  (\ (Ranked x _) -> x)
  (\ (Ranked _ y) x -> Ranked x y)

unranked :: Functor f => Lens' f (Ranked a) a
unranked =
  lens
  (\ (Ranked _ y) -> y)
  (\ (Ranked x _) y -> Ranked x y)

type Rank = Word

new :: a -> ST s (Ref s a)
new = fmap Ref . ST.new . Repr . Ranked minBound

-- |
-- >>> :{
-- runST $ do
--   x <- UnionFind.new 'a'
--   UnionFind.read x
-- :}
-- 'a'
read :: Ref s a -> ST s a
read = mget $ semipruned.repr.unranked

-- |
-- >>> :{
-- runST $ do
--   x <- UnionFind.new 'a'
--   UnionFind.write x 'b'
--   UnionFind.read x
-- :}
-- 'b'
write :: Ref s a -> a -> ST s ()
write ref x = do
  s <- semiprune ref
  writeReprRef s $! Repr $! s^.repr&unranked .~ x

-- |
-- >>> :{
-- runST $ do
--   x <- UnionFind.new 'a'
--   UnionFind.modify x succ
--   UnionFind.read x
-- :}
-- 'b'
modify :: Ref s a -> (a -> a) -> ST s ()
modify ref f = semiprune ref >>= flip modifySemipruned f

-- |
-- >>> :{
-- runST $ do
--   x <- UnionFind.new 'a'
--   y <- UnionFind.new 'b'
--   union x y
--   UnionFind.write y 'c'
--   UnionFind.read x
-- :}
-- 'c'
union :: Ref s a -> Ref s a -> ST s ()
union ref1 ref2 = do
  s1 <- semiprune ref1
  s2 <- semiprune ref2
  when (s1^.reprRef /= s2^.reprRef) $
    case compare (s1^.repr.rank) (s2^.repr.rank) of
     LT ->
       writeReprRef s1 $! Link $! s2^.reprRef
     EQ -> do
       writeReprRef s1 $! Repr $! s1^.repr&rank +~ 1
       writeReprRef s2 $! Link $! s1^.reprRef
     GT ->
       writeReprRef s2 $! Link $! s1^.reprRef

data Semipruned s a =
  Semipruned
  {-# UNPACK #-} !(Ranked a)
  {-# UNPACK #-} !(ST.Ref s (Value s a))

repr :: Functor f => Lens' f (Semipruned s a) (Ranked a)
repr =
  lens
  (\ (Semipruned x _) -> x)
  (\ (Semipruned _ y) x -> Semipruned x y)

reprRef :: Functor f => Lens' f (Semipruned s a) (ST.Ref s (Value s a))
reprRef =
  lens
  (\ (Semipruned _ y) -> y)
  (\ (Semipruned x _) y -> Semipruned x y)

semipruned :: Effective (ST s) r f => Lens' f (Ref s a) (Semipruned s a)
semipruned = mgetter semiprune

semiprune :: Ref s a -> ST s (Semipruned s a)
semiprune = coerce >>> fix (\ rec' ref -> ST.read ref >>= \ case
  Repr x ->
    pure $! Semipruned x ref
  Link ref' -> do
    s <- rec' ref'
    ST.write ref $! Link $! s^.reprRef
    pure s)

writeReprRef :: Semipruned s a -> Value s a -> ST s ()
writeReprRef = ST.write . get reprRef

modifySemipruned :: Semipruned s a -> (a -> a) -> ST s ()
modifySemipruned s f = ST.write (s^.reprRef) (Repr (f <$> s^.repr))
