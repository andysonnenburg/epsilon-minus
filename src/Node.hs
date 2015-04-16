{-# LANGUAGE LambdaCase #-}
module Node
       ( Node
       , BindingFlag (..)
       , new
       , Matchable (..)
       ) where

import Contents
import Control.Monad.ST
import Lens
import Path (Path)
import qualified Path
import qualified UnionFind

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

type RebindRef s f = UnionFind.Ref s (Binder s f)

type UnifyRef s f = UnionFind.Ref s (NodeState s f)

type NodeState s f = (Binder s f, BindingFlag, f (Node s f), Color)

binder :: Functor t => Lens' t (NodeState s f) (Binder s f)
binder =
  lens
  (\ (a, _, _, _) -> a)
  (\ (_, b, c, d) a -> (a, b, c, d))

bindingFlag :: Functor t => Lens' t (NodeState s f) BindingFlag
bindingFlag =
  lens
  (\ (_, b, _, _) -> b)
  (\ (a, _, c, d) b -> (a, b, c, d))

nodes :: Functor t => Lens' t (NodeState s f) (f (Node s f))
nodes =
  lens
  (\ (_, _, c, _) -> c)
  (\ (a, b, _, d) c -> (a, b, c, d))

color :: Functor t => Lens' t (NodeState s f) Color
color =
  lens
  (\ (_, _, _, d) -> d)
  (\ (a, b, c, _) d -> (a, b, c, d))

type MorphismRef s = UnionFind.Ref s Morphism

type Binder s f = Path (Node s f)

data BindingFlag = Flexible | Rigid deriving (Eq, Ord)

data Morphism = Monomorphic | Inert | Polymorphic deriving (Eq, Ord)

data Color = Green | Orange | Red deriving (Eq, Ord)

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

new :: Matchable f => Node s f -> BindingFlag -> f (Node s f) -> ST s (Node s f)
new n bf ns = do
  rr <- UnionFind.new =<< Path.cons n <$> n^!rebindRef.contents
  b <- Path.cons n <$> n^!unifyRef.contents.binder
  c <- getColor n bf
  ur <- UnionFind.new (b, bf, ns, c)
  let m = morphism ns
  mr <- UnionFind.new m
  setMorphism n m bf
  pure $ Node rr ur mr

getColor :: Node s f -> BindingFlag -> ST s Color
getColor n bf = mkColor <$> n^!unifyRef.contents.color <*> pure bf

mkColor :: Color -> BindingFlag -> Color
mkColor = curry $ \ case
  (_, Rigid) -> Orange
  (Green, Flexible) -> Green
  (Orange, Flexible) -> Red
  (Red, Flexible) -> Red

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

class Matchable f where
  zipMatch :: f a -> f b -> Maybe (f (a, b))
  bottom :: f a -> Bool
  polymorphic :: f a -> Bool
  polymorphic = bottom
