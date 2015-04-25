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

class Traversable f => Vertex f where
  isBottom :: f a -> Bool

class Vertex f => LabeledVertex f where
  vertexLabel :: f a -> Int

type Unifiable f = (Matchable f, LabeledVertex f)

data Ref s f =
  Ref
  {-# UNPACK #-} !(RebindRef s f)
  {-# UNPACK #-} !(UnifyRef s f)
  {-# UNPACK #-} !(MorphismRef s)

rebindRef :: Functor t => Lens' t (Ref s f) (RebindRef s f)
rebindRef =
  lens
  (\ (Ref x _ _) -> x)
  (\ (Ref _ y z) x -> Ref x y z)

unifyRef :: Functor t => Lens' t (Ref s f) (UnifyRef s f)
unifyRef =
  lens
  (\ (Ref _ y _) -> y)
  (\ (Ref x _ z) y -> Ref x y z)

morphismRef :: Functor t => Lens' t (Ref s f) (MorphismRef s)
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
new :: Vertex f => Ref s f -> BindingFlag -> f (Ref s f) -> ST s (Ref s f)
new ref bf v =
  Ref <$>
  newRebindRef ref <*>
  newUnifyRef ref bf v <*>
  newMorphismRef ref bf v

newUnbound :: Vertex f => f (Ref s f) -> ST s (Ref s f)
newUnbound v =
  Ref <$>
  newUnboundRebindRef <*>
  newUnboundUnifyRef v <*>
  newUnboundMorphismRef v

readBinding :: Ref s f -> ST s (Maybe (Ref s f, BindingFlag))
readBinding ref = do
  s <- ref^!unifyRef.contents
  case Path.uncons (s^.binder) of
    Nothing -> pure Nothing
    Just (ref', _) -> pure $ Just (ref', s^.bindingFlag)

read :: Ref s f -> ST s (f (Ref s f))
read ref = ref^!unifyRef.contents.vertex

type Unify s = MaybeT (ST s)

unify :: Unifiable f => Ref s f -> Ref s f -> Unify s ()
unify ref_x ref_y = do
  rebind ref_x ref_y
  unify' ref_x ref_y

rebind :: Unifiable f => Ref s f -> Ref s f -> Unify s ()
rebind ref_x ref_y = whenM (lift $ ref_x^.rebindRef /== ref_y^.rebindRef) $ do
  lift $ do
    unifyRebindRef ref_x ref_y
    whenM (isBottom <$> ref_x^!unifyRef.contents.vertex) $
      runVisited $ rebindGrafted ref_y
    whenM (isBottom <$> ref_y^!unifyRef.contents.vertex) $
      runVisited $ rebindGrafted ref_x
  MaybeT
    (zipMatch <$>
     ref_x^!unifyRef.contents.vertex <*>
     ref_y^!unifyRef.contents.vertex) >>=
    traverse_ (uncurry rebind)

unifyRebindRef :: Ref s f -> Ref s f -> ST s ()
unifyRebindRef ref_x ref_y =
  unifyRebindState (ref_x^.rebindRef) (ref_y^.rebindRef)

unifyRebindState :: RebindRef s f -> RebindRef s f -> ST s ()
unifyRebindState ref_x ref_y = do
  modifyM ref_x $ \ b_x -> do
    b_y <- ref_y^!contents
    meetRebindState b_x b_y
  UnionFind.union ref_x ref_y

meetRebindState :: RebindState s f -> RebindState s f -> ST s (RebindState s f)
meetRebindState = Path.lcaM ((===) `on` get rebindRef)

rebindGrafted :: Unifiable f => Ref s f -> Visited s ()
rebindGrafted ref' = do
  v' <- lift $ ref'^!unifyRef.contents.vertex
  whenM (isVisited $ vertexLabel v') $ do
    visit $ vertexLabel v'
    for_ v' $ \ ref -> rebindVirtual ref ref'

rebindVirtual :: Unifiable f => Ref s f -> Ref s f -> Visited s ()
rebindVirtual ref ref' = do
  lift $ do
    b_1 <- ref^!rebindRef.contents
    b_2 <- Path.cons ref' <$> ref'^!rebindRef.contents
    UnionFind.write (ref^.rebindRef) =<< meetRebindState b_1 b_2
  rebindGrafted ref

unify' :: Unifiable f => Ref s f -> Ref s f -> Unify s ()
unify' ref_x ref_y =
  whenM (lift $ ref_x^.morphismRef /== ref_y^.morphismRef) $ do
    check ref_x ref_y
    lift $ unifyMorphismRef ref_x ref_y
    MaybeT
      (zipMatch <$>
       ref_x^!unifyRef.contents.vertex <*>
       ref_y^!unifyRef.contents.vertex) >>=
      traverse_ (uncurry unify')
    lift $ do
      unifyUnifyRef ref_x ref_y
      modifyMorphismRef ref_x

unifyMorphismRef :: Ref s f -> Ref s f -> ST s ()
unifyMorphismRef ref_x ref_y = do
  UnionFind.write (ref_x^.morphismRef) Monomorphic
  UnionFind.union (ref_x^.morphismRef) (ref_y^.morphismRef)

-- |
-- >>> :{
-- runST $ do
--   x <- Vertex.newUnbound T
--   y <- Vertex.newUnbound T
--   unifyMorphismRef x y
--   modifyMorphismRef x
--   readMorphism x
-- :}
-- Monomorphic
--
-- >>> :{
-- runST $ do
--   x <- Vertex.newUnbound Z
--   y <- Vertex.newUnbound Z
--   unifyMorphismRef x y
--   modifyMorphismRef x
--   readMorphism x
-- :}
-- Polymorphic
modifyMorphismRef :: Vertex f => Ref s f -> ST s ()
modifyMorphismRef ref = do
  b <- readRebindBinder ref
  m <- morphism <$> readVertex ref
  whenJust (Path.uncons b) $ \ (ref', _) -> do
    bf <- readBindingFlag ref
    setMorphism ref' bf m
  UnionFind.modify (ref^.morphismRef) $ max m

unifyUnifyRef :: Vertex f => Ref s f -> Ref s f -> ST s ()
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
meetVertex :: Vertex f => f a -> f a -> f a
meetVertex v_x v_y = case (isBottom v_x, isBottom v_y) of
  (False, True) -> v_x
  (True, False) -> v_y
  _ -> v_x

check :: (Foldable f, Vertex f) => Ref s f -> Ref s f -> Unify s ()
check ref_x ref_y = do
  b' <- lift $ readRebindBinder ref_x
  (p_x, b_x, bf_x, v_x) <- lift $ readCheckable ref_x
  let b_x' = Path.keep (length b') b_x
  (p_y, b_y, bf_y, v_y) <- lift $ readCheckable ref_y
  let b_y' = Path.keep (length b') b_y
  checkRaise p_x b_x b_x'
  checkRaise p_y b_y b_y'
  let bf' = max bf_x bf_y
  checkWeaken p_x bf_x bf'
  checkWeaken p_y bf_y bf'
  let p' = max p_x p_y
  checkMerge p' b_x' b_y'
  checkGraft p' v_x v_y
  where
    readCheckable ref =
      (,,,) <$>
      getPermission ref <*>
      readBinder ref <*>
      readBindingFlag ref <*>
      readVertex ref

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
checkWeaken p bf bf' = when (p == R && bf /= bf') empty

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
checkGraft :: (Alternative m, Vertex f) => Permission -> f a -> f b -> m ()
checkGraft p v_x v_y = when (p /= G && isBottom v_x /= isBottom v_y) empty

readRebindBinder :: Ref s f -> ST s (Binder s f)
readRebindBinder = mget $ rebindRef.contents

readBinder :: Ref s f -> ST s (Binder s f)
readBinder = mget $ unifyRef.contents.binder

readBindingFlag :: Ref s f -> ST s BindingFlag
readBindingFlag = mget $ unifyRef.contents.bindingFlag

readVertex :: Ref s f -> ST s (f (Ref s f))
readVertex = mget $ unifyRef.contents.vertex

readColor :: Ref s f -> ST s Color
readColor = mget $ unifyRef.contents.color

readMorphism :: Ref s f -> ST s Morphism
readMorphism = mget $ morphismRef.contents

type RebindRef s f = UnionFind.Ref s (RebindState s f)

newRebindRef :: Ref s f -> ST s (RebindRef s f)
newRebindRef ref = Path.cons ref <$> ref^!rebindRef.contents >>= UnionFind.new

newUnboundRebindRef :: ST s (RebindRef s f)
newUnboundRebindRef = UnionFind.new mempty

type RebindState s f = Binder s f

type UnifyRef s f = UnionFind.Ref s (UnifyState s f)

newUnifyRef :: Ref s f -> BindingFlag -> f (Ref s f) -> ST s (UnifyRef s f)
newUnifyRef ref bf v = UnionFind.new =<< getUnifyState ref bf v

newUnboundUnifyRef :: f (Ref s f) -> ST s (UnifyRef s f)
newUnboundUnifyRef = UnionFind.new . unboundUnifyState

type UnifyState s f = (Binder s f, BindingFlag, f (Ref s f), Color)

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

vertex :: Functor t => Lens' t (UnifyState s f) (f (Ref s f))
vertex =
  lens
  (\ (_, _, c, _) -> c)
  (\ (a, b, _, d) c -> (a, b, c, d))

color :: Functor t => Lens' t (UnifyState s f) Color
color =
  lens
  (\ (_, _, _, d) -> d)
  (\ (a, b, c, _) d -> (a, b, c, d))

getUnifyState :: Ref s f -> BindingFlag -> f (Ref s f) -> ST s (UnifyState s f)
getUnifyState ref bf v =
  (,,,) <$>
  (Path.cons ref <$> ref^!unifyRef.contents.binder) <*>
  pure bf <*>
  pure v <*>
  getColor ref bf

unboundUnifyState :: f (Ref s f) -> UnifyState s f
unboundUnifyState v = (mempty, Flexible, v, Green)

type MorphismRef s = UnionFind.Ref s Morphism

newMorphismRef :: Vertex f => Ref s f -> BindingFlag -> f (Ref s f) -> ST s (MorphismRef s)
newMorphismRef ref' bf v = do
  let m = morphism v
  setMorphism ref' bf m
  UnionFind.new m

newUnboundMorphismRef :: Vertex f => f (Ref s f) -> ST s (MorphismRef s)
newUnboundMorphismRef = UnionFind.new . morphism

type Binder s f = Path (Ref s f)

data Morphism = Monomorphic | Inert | Polymorphic deriving (Show, Eq, Ord)

setMorphism :: Ref s f -> BindingFlag -> Morphism -> ST s ()
setMorphism ref bf =
  UnionFind.modify (ref^.morphismRef) . max . flip mkMorphism bf

morphism :: Vertex f => f (Ref s f) -> Morphism
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

getColor :: Ref s f -> BindingFlag -> ST s Color
getColor ref bf = mkColor <$> ref^!unifyRef.contents.color <*> pure bf

mkColor :: Color -> BindingFlag -> Color
mkColor = curry $ \ case
  (_, Rigid) -> Orange
  (Green, Flexible) -> Green
  (Orange, Flexible) -> Red
  (Red, Flexible) -> Red

data Permission = M | I | G | O | R deriving (Eq, Ord)

getPermission :: Ref s f -> ST s Permission
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
