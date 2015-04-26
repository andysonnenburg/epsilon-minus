{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE NoImplicitPrelude #-}
module Vertex
       ( Matchable (..)
       , Vertex (..)
       , LabeledVertex (..)
       , Unifiable
       , Ref
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
import Control.Monad.Trans.State (StateT, evalStateT, gets, modify)
import Data.Bool
import Data.Eq
import Data.Foldable
import Data.Function
import Data.Int (Int)
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Maybe (Maybe (..), maybe)
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
-- >>> import qualified Vertex
--
-- >>> :{
-- let readRefs ref =
--       (,,) <$> readBindingFlag ref <*> readColor ref <*> readMorphism ref
-- :}
--
-- >>> :{
-- data B a = T | F deriving (Show, Functor, Foldable, Traversable)
-- instance Vertex B where
--   isBottom = \ case
--     F -> True
--     _ -> False
-- :}
--
-- >>> :{
-- data N a = Z | S a deriving (Show, Functor, Foldable, Traversable)
-- instance Vertex N where
--   isBottom = \ case
--     Z -> True
--     _ -> False
-- :}

class Traversable f => Matchable f where
  zipMatch :: f a -> f b -> Maybe (f (a, b))

class Traversable v => Vertex v where
  isBottom :: v a -> Bool

class Vertex v => LabeledVertex v where
  vertexLabel :: v a -> Int

type Unifiable v = (Matchable v, LabeledVertex v)

data Ref s v =
  Ref
  {-# UNPACK #-} !(RebindRef s v)
  {-# UNPACK #-} !(UnifyRef s v)
  {-# UNPACK #-} !(MorphismRef s)

rebindRef :: Functor f => Lens' f (Ref s v) (RebindRef s v)
rebindRef =
  lens
  (\ (Ref x _ _) -> x)
  (\ (Ref _ y z) x -> Ref x y z)

unifyRef :: Functor f => Lens' f (Ref s v) (UnifyRef s v)
unifyRef =
  lens
  (\ (Ref _ y _) -> y)
  (\ (Ref x _ z) y -> Ref x y z)

morphismRef :: Functor f => Lens' f (Ref s v) (MorphismRef s)
morphismRef =
  lens
  (\ (Ref _ _ z) -> z)
  (\ (Ref x y _) z -> Ref x y z)

data BindingFlag = Flexible | Rigid deriving (Show, Eq, Ord)

-- |
-- :{
-- runST $ mdo
--   x0 <- Vertex.new x1 Flexible Z
--   x1 <- Vertex.newUnbound (S x0)
--   (,) <$> readRefs x0 <*> readRefs x1
-- :}
-- ((Flexible, Green, Polymorphic), (Flexible, Green, Polymorphic))
--
-- :{
-- runST $ mdo
--   x0 <- Vertex.new x1 Rigid Z
--   x1 <- Vertex.newUnbound (S x0)
--   (,) <$> readRefs x0 <*> readRefs x1
-- :}
-- ((Rigid, Orange, Polymorphic), (Flexible, Green, Polymorphic))
--
-- :{
-- runST $ mdo
--   x0 <- Vertex.new x1 Flexible Z
--   x1 <- Vertex.new x2 Rigid (S x0)
--   x2 <- Vertex.newUnbound (S x1)
--   (,,) <$> readRefs x0 <*> readRefs x1 <*> readRefs x2
-- :}
-- ((Flexible, Red, Polymorphic), (Rigid, Orange, Polymorphic), (Flexible, Green, Inert))
new :: Vertex v => Ref s v -> BindingFlag -> v (Ref s v) -> ST s (Ref s v)
new ref' bf v =
  Ref <$>
  newRebindRef ref' <*>
  newUnifyRef ref' bf v <*>
  newMorphismRef ref' bf v

newUnbound :: Vertex v => v (Ref s v) -> ST s (Ref s v)
newUnbound v =
  Ref <$>
  newUnboundRebindRef <*>
  newUnboundUnifyRef v <*>
  newUnboundMorphismRef v

readBinding :: Ref s v -> ST s (Maybe (Ref s v, BindingFlag))
readBinding ref = do
  s <- ref^!unifyRef.contents
  case Path.uncons (s^.binder) of
    Nothing -> pure Nothing
    Just (ref', _) -> pure $ Just (ref', s^.bindingFlag)

read :: Ref s v -> ST s (v (Ref s v))
read = readVertex

type Unify s = MaybeT (ST s)

unify :: Unifiable v => Ref s v -> Ref s v -> Unify s ()
unify ref_x ref_y = do
  rebind ref_x ref_y
  unify' ref_x ref_y

rebind :: Unifiable v => Ref s v -> Ref s v -> Unify s ()
rebind ref_x ref_y = whenM (lift $ ref_x^.rebindRef /== ref_y^.rebindRef) $ do
  lift $ do
    unifyRebindRef ref_x ref_y
    whenM (isBottom <$> ref_x^!unifyRef.contents.vertex) $
      runVisited $ rebindGrafted ref_y
    whenM (isBottom <$> ref_y^!unifyRef.contents.vertex) $
      runVisited $ rebindGrafted ref_x
  MaybeT
    (zipMatch <$> readVertex ref_x <*> readVertex ref_y) >>=
    traverse_ (uncurry rebind)

unifyRebindRef :: Ref s v -> Ref s v -> ST s ()
unifyRebindRef ref_x ref_y =
  unifyRebindState (ref_x^.rebindRef) (ref_y^.rebindRef)

unifyRebindState :: RebindRef s v -> RebindRef s v -> ST s ()
unifyRebindState ref_x ref_y = do
  modifyM ref_x $ \ b_x -> do
    b_y <- ref_y^!contents
    meetRebindState b_x b_y
  UnionFind.union ref_x ref_y

meetRebindState :: RebindState s v -> RebindState s v -> ST s (RebindState s v)
meetRebindState = Path.lcaM ((===) `on` get rebindRef)

rebindGrafted :: Unifiable v => Ref s v -> Visited s ()
rebindGrafted ref' = do
  v' <- lift $ ref'^!unifyRef.contents.vertex
  whenM (isVisited $ vertexLabel v') $ do
    visit $ vertexLabel v'
    for_ v' $ \ ref -> rebindVirtual ref ref'

rebindVirtual :: Unifiable v => Ref s v -> Ref s v -> Visited s ()
rebindVirtual ref ref' = do
  lift $ do
    b_1 <- ref^!rebindRef.contents
    b_2 <- Path.cons ref' <$> ref'^!rebindRef.contents
    UnionFind.write (ref^.rebindRef) =<< meetRebindState b_1 b_2
  rebindGrafted ref

unify' :: Unifiable v => Ref s v -> Ref s v -> Unify s ()
unify' ref_x ref_y =
  whenM (lift $ ref_x^.morphismRef /== ref_y^.morphismRef) $ do
    check ref_x ref_y
    lift $ unifyMorphismRef ref_x ref_y
    MaybeT
      (zipMatch <$> readVertex ref_x <*> readVertex ref_y) >>=
      traverse_ (uncurry unify')
    lift $ do
      unifyUnifyRef ref_x ref_y
      writeMorphism ref_x =<< morphism <$> readVertex ref_x

unifyMorphismRef :: Ref s v -> Ref s v -> ST s ()
unifyMorphismRef ref_x ref_y =
  unifyMorphism (ref_x^.morphismRef) (ref_y^.morphismRef)

unifyMorphism :: MorphismRef s -> MorphismRef s -> ST s ()
unifyMorphism ref_x ref_y = do
  UnionFind.write ref_x Monomorphic
  UnionFind.union ref_x ref_y

unifyUnifyRef :: Vertex v => Ref s v -> Ref s v -> ST s ()
unifyUnifyRef ref_x ref_y = do
  b' <- readRebindBinder ref_x
  bf' <- max <$> readBindingFlag ref_x <*> readBindingFlag ref_y
  v' <- meetVertex <$> readVertex ref_x <*> readVertex ref_y
  c' <- max <$> readColor ref_x <*> readColor ref_y
  UnionFind.write (ref_x^.unifyRef) (b', bf', v', c')
  UnionFind.union (ref_x^.unifyRef) (ref_x^.unifyRef)

-- |
-- >>> meetVertex T F
-- T
-- >>> meetVertex F T
-- T
-- >>> meetVertex T T
-- T
-- >>> meetVertex F F
-- F
meetVertex :: Vertex v => v a -> v a -> v a
meetVertex v_x v_y = case (isBottom v_x, isBottom v_y) of
  (False, True) -> v_x
  (True, False) -> v_y
  _ -> v_x

check :: (Foldable v, Vertex v) => Ref s v -> Ref s v -> Unify s ()
check ref_x ref_y = do
  b' <- lift $ readRebindBinder ref_x
  (b_x, bf_x, v_x, p_x) <- lift $ getCheckState ref_x
  let b_x' = Path.keep (length b') b_x
  (b_y, bf_y, v_y, p_y) <- lift $ getCheckState ref_y
  let b_y' = Path.keep (length b') b_y
  checkRaise p_x b_x b_x'
  checkRaise p_y b_y b_y'
  checkWeaken p_x bf_x bf_y
  checkWeaken p_y bf_y bf_x
  checkMerge p_x b_x' b_y'
  checkMerge p_y b_y' b_x'
  checkGraft p_x v_x v_y
  checkGraft p_y v_y v_x

getCheckState :: Ref s v -> ST s (Binder s v, BindingFlag, v (Ref s v), Permission)
getCheckState ref =
  (,,,) <$>
  readBinder ref <*>
  readBindingFlag ref <*>
  readVertex ref <*>
  getPermission ref

checkRaise :: Permission -> Binder s f -> Binder s f -> Unify s ()
checkRaise p b b' =
  when (p == R) $ case (Path.uncons b, Path.uncons b') of
    (Nothing, Nothing) ->
      pure ()
    (Just (ref, _), Just (ref', _)) ->
      whenM (lift $ ref^.rebindRef /== ref'^.rebindRef) empty
    _ ->
      empty

-- |
-- >>> checkWeaken R Flexible Rigid :: Maybe ()
-- Nothing
-- >>> checkWeaken R Rigid Rigid :: Maybe ()
-- Just ()
-- >>> checkWeaken R Flexible Flexible :: Maybe ()
-- Just ()
-- >>> checkWeaken O Flexible Rigid :: Maybe ()
-- Just ()
checkWeaken :: Alternative m => Permission -> BindingFlag -> BindingFlag -> m ()
checkWeaken p bf_x bf_y = when (p == R && bf_x /= bf_y) empty

checkMerge :: Permission -> Binder s f -> Binder s f -> Unify s ()
checkMerge p b_x b_y =
  when (p == R) $ case (Path.uncons b_x, Path.uncons b_y) of
    (Nothing, Nothing) ->
      empty
    (Just (ref_x, _), Just (ref_y, _)) ->
      whenM (lift $ ref_x^.unifyRef === ref_y^.unifyRef) empty
    _ ->
      pure ()

-- |
-- >>> checkGraft R T F :: Maybe ()
-- Nothing
-- >>> checkGraft O F T :: Maybe ()
-- Nothing
-- >>> checkGraft G T F :: Maybe ()
-- Just ()
-- >>> checkGraft R T T :: Maybe ()
-- Just ()
-- >>> checkGraft R F F :: Maybe ()
-- Just ()
checkGraft :: (Alternative m, Vertex v) => Permission -> v a -> v b -> m ()
checkGraft p v_x v_y = when (p /= G && isBottom v_x /= isBottom v_y) empty

readRebindBinder :: Ref s v -> ST s (Binder s v)
readRebindBinder = mget $ rebindRef.contents

readBinder :: Ref s v -> ST s (Binder s v)
readBinder = mget $ unifyRef.contents.binder

readBindingFlag :: Ref s v -> ST s BindingFlag
readBindingFlag = mget $ unifyRef.contents.bindingFlag

readVertex :: Ref s v -> ST s (v (Ref s v))
readVertex = mget $ unifyRef.contents.vertex

readColor :: Ref s v -> ST s Color
readColor = mget $ unifyRef.contents.color

readMorphism :: Ref s v -> ST s Morphism
readMorphism = mget $ morphismRef.contents

type RebindRef s v = UnionFind.Ref s (RebindState s v)

newRebindRef :: Ref s v -> ST s (RebindRef s v)
newRebindRef ref' = Path.cons ref' <$> ref'^!rebindRef.contents >>= UnionFind.new

newUnboundRebindRef :: ST s (RebindRef s v)
newUnboundRebindRef = UnionFind.new mempty

type RebindState s v = Binder s v

type UnifyRef s v = UnionFind.Ref s (UnifyState s v)

newUnifyRef :: Ref s v -> BindingFlag -> v (Ref s v) -> ST s (UnifyRef s v)
newUnifyRef ref' bf v = UnionFind.new =<< getUnifyState ref' bf v

newUnboundUnifyRef :: v (Ref s v) -> ST s (UnifyRef s v)
newUnboundUnifyRef = UnionFind.new . unboundUnifyState

type UnifyState s v = (Binder s v, BindingFlag, v (Ref s v), Color)

binder :: Functor f => Lens' f (UnifyState s v) (Binder s v)
binder =
  lens
  (\ (a, _, _, _) -> a)
  (\ (_, b, c, d) a -> (a, b, c, d))

bindingFlag :: Functor f => Lens' f (UnifyState s v) BindingFlag
bindingFlag =
  lens
  (\ (_, b, _, _) -> b)
  (\ (a, _, c, d) b -> (a, b, c, d))

vertex :: Functor f => Lens' f (UnifyState s v) (v (Ref s v))
vertex =
  lens
  (\ (_, _, c, _) -> c)
  (\ (a, b, _, d) c -> (a, b, c, d))

color :: Functor f => Lens' f (UnifyState s v) Color
color =
  lens
  (\ (_, _, _, d) -> d)
  (\ (a, b, c, _) d -> (a, b, c, d))

getUnifyState :: Ref s v -> BindingFlag -> v (Ref s v) -> ST s (UnifyState s v)
getUnifyState ref' bf v =
  (,,,) <$>
  (Path.cons ref' <$> readBinder ref') <*>
  pure bf <*>
  pure v <*>
  getColor ref' bf

unboundUnifyState :: v (Ref s v) -> UnifyState s v
unboundUnifyState v = (mempty, Flexible, v, Green)

type MorphismRef s = UnionFind.Ref s Morphism

newMorphismRef :: Vertex v => Ref s v -> BindingFlag -> v (Ref s v) -> ST s (MorphismRef s)
newMorphismRef ref' bf v = do
  let m = morphism v
  writeParentMorphism ref' bf m
  UnionFind.new m

newUnboundMorphismRef :: Vertex v => v (Ref s v) -> ST s (MorphismRef s)
newUnboundMorphismRef = UnionFind.new . morphism

type Binder s v = Path (Ref s v)

data Morphism = Monomorphic | Inert | Polymorphic deriving (Show, Eq, Ord)

-- |
-- >>> :{
-- runST $ do
--   x <- Vertex.newUnbound T
--   y <- Vertex.newUnbound T
--   unifyMorphismRef x y
--   writeMorphism x =<< morphism <$> readVertex x
--   readMorphism x
-- :}
-- Monomorphic
--
-- >>> :{
-- runST $ do
--   x <- Vertex.newUnbound Z
--   y <- Vertex.newUnbound Z
--   unifyMorphismRef x y
--   writeMorphism x =<< morphism <$> readVertex x
--   readMorphism x
-- :}
-- Polymorphic
writeMorphism :: Ref s v -> Morphism -> ST s ()
writeMorphism ref m = do
  writeBinderMorphism ref m
  UnionFind.modify (ref^.morphismRef) $ max m

writeBinderMorphism :: Ref s v -> Morphism -> ST s ()
writeBinderMorphism ref m = do
  b <- readRebindBinder ref
  whenJust (Path.uncons b) $ \ (ref', _) -> do
    bf <- readBindingFlag ref
    writeParentMorphism ref' bf m

writeParentMorphism :: Ref s v -> BindingFlag -> Morphism -> ST s ()
writeParentMorphism ref' bf =
  UnionFind.modify (ref'^.morphismRef) . max . flip mkMorphism bf

morphism :: Vertex v => v (Ref s v) -> Morphism
morphism v
  | isBottom v = Polymorphic
  | otherwise = Monomorphic

mkMorphism :: Morphism -> BindingFlag -> Morphism
mkMorphism = curry $ \ case
  (Monomorphic, _) -> Monomorphic
  (Inert, _) -> Inert
  (Polymorphic, Flexible) -> Polymorphic
  (Polymorphic, Rigid) -> Inert

data Color = Green | Orange | Red deriving (Eq, Ord)

getColor :: Ref s v -> BindingFlag -> ST s Color
getColor ref bf = mkColor <$> ref^!unifyRef.contents.color <*> pure bf

mkColor :: Color -> BindingFlag -> Color
mkColor = curry $ \ case
  (_, Rigid) -> Orange
  (Green, Flexible) -> Green
  (Orange, Flexible) -> Red
  (Red, Flexible) -> Red

data Permission = M | I | G | O | R deriving (Eq, Ord)

getPermission :: Ref s v -> ST s Permission
getPermission ref = mkPermission <$> readColor ref <*> readMorphism ref

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
whenM p m = p >>= bool (pure ()) m

whenJust :: Applicative m => Maybe a -> (a -> m ()) -> m ()
whenJust p f = maybe (pure ()) f p

type Visited s = StateT IntSet (ST s)

runVisited :: Visited s a -> ST s a
runVisited = flip evalStateT mempty

isVisited :: Int -> Visited s Bool
isVisited = gets . IntSet.notMember

visit :: Int -> Visited s ()
visit = modify . IntSet.insert
