{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NoImplicitPrelude #-}
module Node
       ( Matchable (..)
       , Unifiable (..)
       , Inferable (..)
       , Node
       , BindingFlag (..)
       , new
       , newUnbound
       , readBinding
       , read
       , unify
       ) where

import Contents
import Control.Applicative
import Control.Monad
import Control.Monad.ST
import Control.Monad.Trans.Class
import Control.Monad.Trans.Maybe
import Data.Bool
import Data.Eq
import Data.Foldable
import Data.Function
import Data.Int (Int)
import Data.Maybe (Maybe (..))
import Data.Monoid
import Data.Ord
import Data.Traversable
import Data.Tuple
import Lens
import Path (Path)
import qualified Path
import Text.Show
import UnionFind ((/==), (===))
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

class Traversable f => Matchable f where
  zipMatch :: f a -> f b -> Maybe (f (a, b))

class Matchable f => Unifiable f where
  isBottom :: f a -> Bool

class Unifiable f => Inferable f where
  toInt :: f a -> Int

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

data BindingFlag = Flexible | Rigid deriving (Show, Eq, Ord)

-- |
-- >>> :{
-- data N a = Z | S a deriving (Show, Functor, Foldable, Traversable)
-- instance Matchable N where
--   zipMatch = curry $ \ case
--     (Z, Z) -> Just Z
--     (S x, S y) -> Just (S (x, y))
--     _ -> Nothing
-- instance Unifiable N where
--   isBottom = \ case
--     Z -> True
--     _ -> False
-- :}
--
-- :{
-- runST $ mdo
--   x0 <- Node.new x1 Flexible Z
--   x1 <- Node.newUnbound (S x0)
--   (,) <$> readRefs x0 <*> readRefs x1
-- :}
-- ((Flexible, Green, Polymorphic), (Flexible, Green, Polymorphic))
--
-- :{
-- runST $ mdo
--   x0 <- Node.new x1 Rigid Z
--   x1 <- Node.newUnbound (S x0)
--   (,) <$> readRefs x0 <*> readRefs x1
-- :}
-- ((Rigid, Orange, Polymorphic), (Flexible, Green, Polymorphic))
--
-- :{
-- runST $ mdo
--   x0 <- Node.new x1 Flexible Z
--   x1 <- Node.new x2 Rigid (S x0)
--   x2 <- Node.newUnbound (S x1)
--   (,,) <$> readRefs x0 <*> readRefs x1 <*> readRefs x2
-- :}
-- ((Flexible, Red, Polymorphic), (Rigid, Orange, Polymorphic), (Flexible, Green, Inert))
new :: Unifiable f => Node s f -> BindingFlag -> f (Node s f) -> ST s (Node s f)
new n bf ns =
  Node <$>
  newRebindRef n <*>
  newUnifyRef n bf ns <*>
  newMorphismRef n bf ns

newUnbound :: Unifiable f => f (Node s f) -> ST s (Node s f)
newUnbound ns =
  Node <$>
  newUnboundRebindRef <*>
  newUnboundUnifyRef ns <*>
  newUnboundMorphismRef ns

readBinding :: Node s f -> ST s (Maybe (Node s f, BindingFlag))
readBinding n = do
  s <- n^!unifyRef.contents
  case Path.uncons (s^.binder) of
    Nothing -> pure Nothing
    Just (n', _) -> pure $ Just (n', s^.bindingFlag)

read :: Node s f -> ST s (f (Node s f))
read n = n^!unifyRef.contents.nodes

type Unify s = MaybeT (ST s)

unify :: Unifiable f => Node s f -> Node s f -> Unify s ()
unify n_x n_y = do
  rebind n_x n_y
  unify' n_x n_y

rebind :: Unifiable f => Node s f -> Node s f -> Unify s ()
rebind n_x n_y = whenM (lift $ n_x^.rebindRef /== n_y^.rebindRef) $ do
  lift $ do
    unifyRebindRef n_x n_y
    whenM (isBottom <$> n_x^!unifyRef.contents.nodes) $
      traverse_ (flip rebindVirtual n_y) =<< n_y^!unifyRef.contents.nodes
    whenM (isBottom <$> n_y^!unifyRef.contents.nodes) $
      traverse_ (flip rebindVirtual n_x) =<< n_x^!unifyRef.contents.nodes
  MaybeT
    (zipMatch <$>
     n_x^!unifyRef.contents.nodes <*>
     n_y^!unifyRef.contents.nodes) >>=
    traverse_ (uncurry rebind)

unifyRebindRef :: Node s f -> Node s f -> ST s ()
unifyRebindRef n_x n_y = unifyRebindState (n_x^.rebindRef) (n_y^.rebindRef)

unifyRebindState :: RebindRef s f -> RebindRef s f -> ST s ()
unifyRebindState ref_x ref_y = do
  modifyM ref_x $ \ b_x -> do
    b_y <- ref_y^!contents
    meetRebindState b_x b_y
  UnionFind.union ref_x ref_y

meetRebindState :: RebindState s f -> RebindState s f -> ST s (RebindState s f)
meetRebindState = Path.lcaM ((===) `on` get rebindRef)

rebindVirtual :: Foldable f => Node s f -> Node s f -> ST s ()
rebindVirtual n n' = do
  modifyM (n^.rebindRef) $ \ b_1 -> do
    b_2 <- Path.cons n' <$> n'^!rebindRef.contents
    meetRebindState b_1 b_2
  traverse_ (flip rebindVirtual n) =<< n^!unifyRef.contents.nodes

unify' :: Unifiable f => Node s f -> Node s f -> Unify s ()
unify' n_x n_y = whenM (lift $ n_x^.unifyRef /== n_y^.unifyRef) $ do
  MaybeT
    (zipMatch <$>
     n_x^!unifyRef.contents.nodes <*>
     n_y^!unifyRef.contents.nodes) >>=
     traverse_ (uncurry unify')

type RebindRef s f = UnionFind.Ref s (RebindState s f)

newRebindRef :: Node s f -> ST s (RebindRef s f)
newRebindRef n = Path.cons n <$> n^!rebindRef.contents >>= UnionFind.new

newUnboundRebindRef :: ST s (RebindRef s f)
newUnboundRebindRef = UnionFind.new mempty

type RebindState s f = Binder s f

type UnifyRef s f = UnionFind.Ref s (UnifyState s f)

newUnifyRef :: Node s f -> BindingFlag -> f (Node s f) -> ST s (UnifyRef s f)
newUnifyRef n bf ns = UnionFind.new =<< getUnifyState n bf ns

newUnboundUnifyRef :: f (Node s f) -> ST s (UnifyRef s f)
newUnboundUnifyRef = UnionFind.new . unboundUnifyState

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

unboundUnifyState :: f (Node s f) -> UnifyState s f
unboundUnifyState ns = (mempty, Flexible, ns, Green)

type MorphismRef s = UnionFind.Ref s Morphism

newMorphismRef :: Unifiable f => Node s f -> BindingFlag -> f (Node s f) -> ST s (MorphismRef s)
newMorphismRef n bf ns = do
  let m = morphism ns
  setMorphism n m bf
  UnionFind.new m

newUnboundMorphismRef :: Unifiable f => f (Node s f) -> ST s (MorphismRef s)
newUnboundMorphismRef = UnionFind.new . morphism

type Binder s f = Path (Node s f)

data Morphism = Monomorphic | Inert | Polymorphic deriving (Eq, Ord)

setMorphism :: Node s f -> Morphism -> BindingFlag -> ST s ()
setMorphism n m = UnionFind.modify (n^.morphismRef) . max . mkMorphism m

morphism :: Unifiable f => f (Node s f) -> Morphism
morphism xs
  | isBottom xs = Polymorphic
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

modifyM :: UnionFind.Ref s a -> (a -> ST s a) -> ST s ()
modifyM ref f = UnionFind.write ref =<< f =<< UnionFind.read ref

whenM :: Monad m => m Bool -> m () -> m ()
whenM p m = p >>= bool (return ()) m
