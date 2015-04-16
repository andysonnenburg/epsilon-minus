{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Contents
       ( Contents (..)
       ) where

import Control.Monad.ST
import Lens
import qualified ST
import qualified UnionFind

class Monad m => Contents m ref where
  contents :: Effective m r f => Lens' f (ref a) a

instance Contents (ST s) (ST.Ref s) where
  contents = mgetter ST.read

instance Contents (ST s) (UnionFind.Ref s) where
  contents = mgetter UnionFind.read
