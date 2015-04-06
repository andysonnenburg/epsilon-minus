{-# LANGUAGE NoImplicitPrelude #-}
module ST
       ( Ref
       , new
       , read
       , write
       ) where

import Control.Monad.ST
import Data.STRef

type Ref = STRef

new :: a -> ST s (Ref s a)
new = newSTRef

read :: Ref s a -> ST s a
read = readSTRef

write :: Ref s a -> a -> ST s ()
write = writeSTRef
