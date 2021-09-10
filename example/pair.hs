module pair

import prelude

data pair (a b : Type): Type where
  mk : a -o b -o pair a b

fst : Pi {0 a b : Type}, pair a b -> a
fst (mk x y) = x

snd : Pi {0 a b : Type}(p : pair a b), b
snd (mk x y) = y

eta : Pi {0 a b : Type}(p : pair a b), eq p (mk (fst p) (snd p))
eta (mk x y) = refl

curry : Pi {0 a b c : Type}, (pair a b -> c) -> a -> b -> c
curry f x y = f (mk x y)

uncurry : Pi {0 a b c : Type}, (a -> b -> c) -> pair a b -> c
uncurry f (mk x y) = f x y

mk_injective : Pi {0 a b c : Type}
                  {0 x1 x2 : a}
                  {0 y1 y2 : b},
                  eq (mk x1 y1) (mk x2 y2) =>
                  (eq x1 x2 => eq y1 y2 => c) ->
                  c
mk_injective refl f = f refl refl
