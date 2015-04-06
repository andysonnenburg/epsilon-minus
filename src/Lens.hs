module Lens
       ( (&)
       , Lens
       , Lens'
       , lens
       , get
       , (^.)
       , set
       , (.~)
       , (+~)
       ) where

import Control.Applicative
import Data.Functor.Identity

infixl 1 &
infixr 4 .~, +~
infixl 8 ^.

(&) :: a -> (a -> b) -> b
(&) = flip ($)

type Lens f s t a b = (a -> f b) -> s -> f t

type Lens' f s a = Lens f s s a a

lens :: Functor f => (s -> a) -> (s -> b -> t) -> Lens f s t a b
lens get' set' f s = set' s <$> f (get' s)

get :: ((a -> Const a b) -> s -> Const a t) -> s -> a
get l = getConst . l Const

(^.) :: s -> ((a -> Const a b) -> s -> Const a t) -> a
(^.) = flip get

set :: ((a -> Identity b) -> s -> Identity t) -> b -> s -> t
set l b = runIdentity . l (const $ Identity b)

(.~) :: ((a -> Identity b) -> s -> Identity t) -> b -> s -> t
(.~) = set

(+~) :: Num a => ((a -> Identity a) -> s -> Identity t) -> a -> s -> t
(+~) l a = runIdentity . l (Identity . (+ a))
