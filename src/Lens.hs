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

get :: Lens (Const a) s t a b -> s -> a
get l = getConst . l Const

(^.) :: s -> Lens (Const a) s t a b -> a
(^.) = flip get

set :: Lens Identity s t a b -> b -> s -> t
set l b = runIdentity . l (const $ Identity b)

(.~) :: Lens Identity s t a b -> b -> s -> t
(.~) = set

(+~) :: Num a => Lens Identity s t a a -> a -> s -> t
(+~) l a = runIdentity . l (Identity . (+ a))
