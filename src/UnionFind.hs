{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NoImplicitPrelude #-}
module UnionFind
       ( Ref
       , new
       , read
       , write
       , union
       ) where

import Control.Applicative
import Control.Category
import Control.Monad
import Control.Monad.ST
import Data.Coerce
import Data.Function (($), fix)
import Data.Ord
import Data.Word
import Prelude (($!), (/=), (+), minBound)
import qualified ST

newtype Ref s a = Ref (ST.Ref s (Value s a))

data Value s a
  = Repr {-# UNPACK #-} !(Ranked a)
  | Link {-# UNPACK #-} !(ST.Ref s (Value s a))

data Ranked a = Ranked { rank :: {-# UNPACK #-} !Rank, unranked :: a }

type Rank = Word

new :: a -> ST s (Ref s a)
new = coerce . ST.new . Repr . Ranked minBound

read :: Ref s a -> ST s a
read = fmap (unranked . repr) . semiprune

write :: Ref s a -> a -> ST s ()
write ref x = do
  s <- semiprune ref
  writeReprRef s $! Repr $! (repr s) { unranked = x }

union :: Ref s a -> Ref s a -> ST s ()
union ref1 ref2 = do
  s1 <- semiprune ref1
  s2 <- semiprune ref2
  when (reprRef s1 /= reprRef s2) $
    case compare (rank $ repr s1) (rank $ repr s2) of
     LT ->
       writeReprRef s1 $! Link $! reprRef s2
     EQ -> do
       writeReprRef s1 $! Repr $! (repr s1) { rank = rank (repr s1) + 1 }
       writeReprRef s2 $! Link $! reprRef s1
     GT ->
       writeReprRef s2 $! Link $! reprRef s1

data Semipruned s a =
  Semipruned
  { repr :: {-# UNPACK #-} !(Ranked a)
  , reprRef :: {-# UNPACK #-} !(ST.Ref s (Value s a))
  }

semiprune :: Ref s a -> ST s (Semipruned s a)
semiprune = coerce >>> fix (\ rec' ref -> ST.read ref >>= \ case
  Repr x ->
    pure $! Semipruned x ref
  Link ref' -> do
    s <- rec' ref'
    ST.write ref $! Link $! reprRef s
    pure s)

writeReprRef :: Semipruned s a -> Value s a -> ST s ()
writeReprRef = ST.write . reprRef
