{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Lens
       ( (&)
       , Lens
       , Lens'
       , Getter
       , Setter
       , lens
       , get
       , (^.)
       , Effective (..)
       , mgetter
       , mget
       , (^!)
       , set
       , (.~)
       , (+~)
       ) where

import Control.Applicative
import Data.Coerce
import Data.Functor.Identity

infixl 1 &
infixr 4 .~, +~
infixl 8 ^., ^!

(&) :: a -> (a -> b) -> b
(&) = flip ($)

type Lens f s t a b = (a -> f b) -> s -> f t

type Lens' f s a = Lens f s s a a

type Getter r s a = Lens' (Const r) s a

type EffectiveGetter m r s a = Lens' (Effect m r) s a

type Setter s t a b = Lens Identity s t a b

lens :: Functor f => (s -> a) -> (s -> b -> t) -> Lens f s t a b
lens get' set' f s = set' s <$> f (get' s)

get :: Getter a s a -> s -> a
get l = getConst . l Const

(^.) :: s -> Getter a s a -> a
(^.) = flip get

class (Monad m, Functor f) => Effective m r f | f -> m r where
  effective :: m r -> f a
  default effective :: Coercible (m r) (f a) => m r -> f a
  effective = coerce
  
  ineffective :: f a -> m r
  default ineffective :: Coercible (f a) (m r) => f a -> m r
  ineffective = coerce

instance Effective Identity r (Const r)

newtype Effect m r a = Effect (Const (m r) a) deriving (Functor, Applicative)

instance Monad m => Effective m r (Effect m r)

mgetter :: Effective m r f => (s -> m a) -> Lens' f s a
mgetter k f s = effective (k s >>= ineffective . f)

mget :: Applicative m => EffectiveGetter m a s a -> s -> m a
mget l = coerce . l (Effect . Const . pure)

(^!) :: Applicative m => s -> EffectiveGetter m a s a -> m a
(^!) = flip mget

set :: Setter s t a b -> b -> s -> t
set l b = runIdentity . l (const $ Identity b)

(.~) :: Setter s t a b -> b -> s -> t
(.~) = set

(+~) :: Num a => Setter s t a a -> a -> s -> t
(+~) l a = runIdentity . l (Identity . (+ a))
