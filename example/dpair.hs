module dpair

import prelude

data dpair(a : Type)(b : a -> Type): Type where
  mk : Pi 1 x : a, b x -o dpair a b

p1 : Pi {0 a : Type}{0 b : a -> Type}, dpair a b -> a
p1 (mk x y) = x

p2 : Pi {0 a : Type}{0 b : a -> Type}(p : dpair a b), b (p1 p)
p2 (mk x y) = y

curry : Pi {0 a c : Type}{0 b : a -> Type}, (Pi x : a, b x -> c) -> dpair a b -> c
curry f (mk x y) = f x y

uncurry: Pi {0 a c : Type}{0 b : a -> Type}, (dpair a b -> c) -> Pi x : a, b x -> c
uncurry f x y = f (mk x y)

eta : Pi {0 a : Type}{0 b : a -> Type}(p : dpair a b), eq p (mk (p1 p) (p2 p))
eta (mk x y) = refl

mk_injective : Pi
  {0 a c : Type}
  {0 b : a -> Type}
  {0 x1 x2 : a}
  {0 y1 : b x1}
  {0 y2 : b x2},
    eq (mk x1 y1) (mk x2 y2) => 
    (Pi 0 e : eq x1 x2, eq (subst b e y1) y2 => c) -> c
mk_injective refl f = f refl refl
