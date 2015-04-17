{-# LANGUAGE LambdaCase #-}
module Node
       ( Node
       , new
       , newRoot
       , unify
       , Matchable (..)
       , BindingFlag (..)
       ) where

import Contents
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Maybe
import Control.Monad.ST
import Data.Bool
import Data.Foldable
import Data.Function
import Lens
import Path (Path)
import qualified Path
import UnionFind ((===), (/==))
import qualified UnionFind

-- $setup
-- >>> :set -XLambdaCase
-- >>> :set -XRecursiveDo
-- >>> :set -XDeriveFunctor
-- >>> :set -XDeriveFoldable
-- >>> :set -XFlexibleContexts
-- >>> :set -XDeriveTraversable
-- >>> import qualified Node
--
-- >>> :{
-- let readUnifyRef n = do
--       (_, bf, _, c) <- n^!unifyRef.contents
--       pure (bf, c)
-- :}
--
-- >>> :{
-- let readMorphismRef n = n^!morphismRef.contents
-- :}
--
-- >>> :{
-- let readRefs n = do
--       (bf, c) <- readUnifyRef n
--       m <- readMorphismRef n
--       pure (bf, c, m)
-- :}

data Node s f =
  Node
  {-# UNPACK #-} !(RebindRef s f)
  {-# UNPACK #-} !(UnifyRef s f)
  {-# UNPACK #-} !(MorphismRef s)

rebindRef :: Functor t => Lens' t (Node s f) (RebindRef s f)
rebindRef =
  lens
  (\ (Node x _ _) -> x)
  (\ (Node _ y z) x -> Node x y z)

unifyRef :: Functor t => Lens' t (Node s f) (UnifyRef s f)
unifyRef =
  lens
  (\ (Node _ y _) -> y)
  (\ (Node x _ z) y -> Node x y z)

morphismRef :: Functor t => Lens' t (Node s f) (MorphismRef s)
morphismRef =
  lens
  (\ (Node _ _ z) -> z)
  (\ (Node x y _) z -> Node x y z)

-- |
-- >>> :{
-- data N a = Z | S a deriving (Show, Functor, Foldable, Traversable)
-- instance Matchable N where
--   zipMatch = curry $ \ case
--     (Z, Z) -> Just Z
--     (S x, S y) -> Just (S (x, y))
--     _ -> Nothing
--   bottom = \ case
--     Z -> True
--     _ -> False
-- :}
--
-- :{
-- runST $ mdo
--   x0 <- Node.new x1 Flexible Z
--   x1 <- Node.newRoot (S x0)
--   (,) <$> readRefs x0 <*> readRefs x1
-- :}
-- ((Flexible, Green, Polymorphic), (Flexible, Green, Polymorphic))
--
-- :{
-- runST $ mdo
--   x0 <- Node.new x1 Rigid Z
--   x1 <- Node.newRoot (S x0)
--   (,) <$> readRefs x0 <*> readRefs x1
-- :}
-- ((Rigid, Orange, Polymorphic), (Flexible, Green, Polymorphic))
--
-- :{
-- runST $ mdo
--   x0 <- Node.new x1 Flexible Z
--   x1 <- Node.new x2 Rigid (S x0)
--   x2 <- Node.newRoot (S x1)
--   (,,) <$> readRefs x0 <*> readRefs x1 <*> readRefs x2
-- :}
-- ((Flexible, Red, Polymorphic), (Rigid, Orange, Polymorphic), (Flexible, Green, Inert))
new :: Matchable f => Node s f -> BindingFlag -> f (Node s f) -> ST s (Node s f)
new n bf ns =
  Node <$>
  newRebindRef n <*>
  newUnifyRef n bf ns <*>
  newMorphismRef n bf ns

newRoot :: Matchable f => f (Node s f) -> ST s (Node s f)
newRoot ns =
  Node <$>
  newRootRebindRef <*>
  newRootUnifyRef ns <*>
  newRootMorphismRef ns

type Unify s = MaybeT (ST s)

unify :: Matchable f => Node s f -> Node s f -> Unify s ()
unify n_x n_y =
  rebind n_x n_y

rebind :: Matchable f => Node s f -> Node s f -> Unify s ()
rebind n_x n_y = whenM (lift $ n_x^.rebindRef /== n_y^.rebindRef) $ do
  lift $ do
    b <- join $ lcaM' <$> n_x^!rebindRef.contents <*> n_y^!rebindRef.contents
    UnionFind.union (n_x^.rebindRef) (n_y^.rebindRef)
    UnionFind.write (n_x^.rebindRef) b
  MaybeT
    (zipMatch <$>
     n_x^!unifyRef.contents.nodes <*>
     n_y^!unifyRef.contents.nodes) >>=
    traverse_ (uncurry rebind)
  where
    lcaM' = Path.lcaM ((===) `on` get rebindRef)

class Traversable f => Matchable f where
  zipMatch :: f a -> f b -> Maybe (f (a, b))
  bottom :: f a -> Bool
  polymorphic :: f a -> Bool
  polymorphic = bottom

type RebindRef s f = UnionFind.Ref s (RebindState s f)

newRebindRef :: Node s f -> ST s (RebindRef s f)
newRebindRef n = Path.cons n <$> n^!rebindRef.contents >>= UnionFind.new

newRootRebindRef :: ST s (RebindRef s f)
newRootRebindRef = UnionFind.new mempty

type RebindState s f = Binder s f

type UnifyRef s f = UnionFind.Ref s (UnifyState s f)

newUnifyRef :: Node s f -> BindingFlag -> f (Node s f) -> ST s (UnifyRef s f)
newUnifyRef n bf ns = UnionFind.new =<< getUnifyState n bf ns

newRootUnifyRef :: f (Node s f) -> ST s (UnifyRef s f)
newRootUnifyRef = UnionFind.new . rootUnifyState

type UnifyState s f = (Binder s f, BindingFlag, f (Node s f), Color)

binder :: Functor t => Lens' t (UnifyState s f) (Binder s f)
binder =
  lens
  (\ (a, _, _, _) -> a)
  (\ (_, b, c, d) a -> (a, b, c, d))

bindingFlag :: Functor t => Lens' t (UnifyState s f) BindingFlag
bindingFlag =
  lens
  (\ (_, b, _, _) -> b)
  (\ (a, _, c, d) b -> (a, b, c, d))

nodes :: Functor t => Lens' t (UnifyState s f) (f (Node s f))
nodes =
  lens
  (\ (_, _, c, _) -> c)
  (\ (a, b, _, d) c -> (a, b, c, d))

color :: Functor t => Lens' t (UnifyState s f) Color
color =
  lens
  (\ (_, _, _, d) -> d)
  (\ (a, b, c, _) d -> (a, b, c, d))

getUnifyState :: Node s f -> BindingFlag -> f (Node s f) -> ST s (UnifyState s f)
getUnifyState n bf ns =
  (,,,) <$>
  (Path.cons n <$> n^!unifyRef.contents.binder) <*>
  pure bf <*>
  pure ns <*>
  getColor n bf

rootUnifyState :: f (Node s f) -> UnifyState s f
rootUnifyState ns = (mempty, Flexible, ns, Green)

type MorphismRef s = UnionFind.Ref s Morphism

newMorphismRef :: Matchable f => Node s f -> BindingFlag -> f (Node s f) -> ST s (MorphismRef s)
newMorphismRef n bf ns = do
  let m = morphism ns
  setMorphism n m bf
  UnionFind.new m

newRootMorphismRef :: Matchable f => f (Node s f) -> ST s (MorphismRef s)
newRootMorphismRef = UnionFind.new . morphism

type Binder s f = Path (Node s f)

data BindingFlag = Flexible | Rigid deriving (Eq, Ord)

data Morphism = Monomorphic | Inert | Polymorphic deriving (Eq, Ord)

setMorphism :: Node s f -> Morphism -> BindingFlag -> ST s ()
setMorphism n m = UnionFind.modify (n^.morphismRef) . max . mkMorphism m

morphism :: Matchable f => f (Node s f) -> Morphism
morphism xs
  | polymorphic xs = Polymorphic
  | otherwise = Monomorphic

mkMorphism :: Morphism -> BindingFlag -> Morphism
mkMorphism = curry $ \ case
  (Monomorphic, _) -> Monomorphic
  (Inert, _) -> Inert
  (Polymorphic, Flexible) -> Polymorphic
  (Polymorphic, Rigid) -> Inert

data Color = Green | Orange | Red deriving (Eq, Ord)

getColor :: Node s f -> BindingFlag -> ST s Color
getColor n bf = mkColor <$> n^!unifyRef.contents.color <*> pure bf

mkColor :: Color -> BindingFlag -> Color
mkColor = curry $ \ case
  (_, Rigid) -> Orange
  (Green, Flexible) -> Green
  (Orange, Flexible) -> Red
  (Red, Flexible) -> Red

data Permission = M | I | G | O | R deriving (Eq, Ord)

getPermission :: Node s f -> ST s Permission
getPermission n =
  mkPermission <$>
  n^!unifyRef.contents.color <*>
  n^!morphismRef.contents

mkPermission :: Color -> Morphism -> Permission
mkPermission = curry $ \ case
  (_, Monomorphic) -> M
  (_, Inert) -> I
  (Green, _) -> G
  (Orange, _) -> O
  (Red, _) -> R

whenM :: Monad m => m Bool -> m () -> m ()
whenM p m = p >>= bool (return ()) m
