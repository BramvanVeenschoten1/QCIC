module prelude

data void : Type where

absurd : Pi {0 a : Type}, void => a
absurd ()

not : Type -> Type
not a = a -> void

data unit : Type where
  tt : unit

data eq {0 a:Type}(x:a): a -> Type where
  refl : eq x x

sym : Pi {0 a : Type}{0 x y : a}, eq x y -> eq y x
sym refl = refl

trans : Pi {0 a : Type}{0 x y z : a}, eq x y -> eq y z -> eq x z
trans refl e = e

J : Pi {0 a : Type}{0 x y : a}(0 p : Pi z : a, eq x z -> Type)(prefl : p x refl)(e : eq x y), p y e
J p prefl refl = prefl

K : Pi {0 a : Type}{0 x : a}(0 p : eq x x -> Type)(prefl : p refl)(e : eq x x), p e
K p prefl refl = prefl

subst : Pi {0 a : Type}{0 x y : a}(0 p : Pi z : a, Type), eq x y -> p x -> p y
subst p refl prefl = prefl

cong : Pi {0 a b : Type}{0 x y : a}(f : a -> b), eq x y -> eq (f x) (f y)
cong f refl = refl

