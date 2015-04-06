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
import Lens
import Prelude (($!), (/=), minBound)
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
  writeReprRef s $! Repr $! s^.repr&_2 .~ x

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
  { repr :: {-# UNPACK #-} !(Ranked a)
  , reprRef :: {-# UNPACK #-} !(ST.Ref s (Value s a))
  }

semiprune :: Ref s a -> ST s (Semipruned s a)
semiprune = coerce >>> fix (\ rec' ref -> ST.read ref >>= \ case
  Repr x ->
    pure $! Semipruned x ref
  Link ref' -> do
    s <- rec' ref'
    ST.write ref $! Link $! s^.reprRef
    pure s)

writeReprRef :: Semipruned s a -> Value s a -> ST s ()
writeReprRef = ST.write . view reprRef
