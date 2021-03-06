module either

import prelude

data either (a b : Type) : Type where
  left  : a -> either a b
  right : b -> either a b

either_ind : Pi {0 a b : Type}
                (0 p : either a b -> Type),
                (Pi x : a, p (left x)) ->
                (Pi x : b, p (right x)) ->
                Pi x : either a b, p x
either_ind p pl pr (left x) = pl x
either_ind p pl pr (right x) = pr x

either_case : Pi {0 a b c : Type}, (a -> c) -> (b -> c) -> either a b -> c
either_case f g (left x) = f x
either_case f g (right x) = g x

decidable : Type -> Type
decidable p = either p (not p)

map : Pi {0 a b e : Type}, (a -> b) -> either e a -> either e b
map f (right x) = right (f x)
map f (left e) = left e

pure : Pi {0 a e : Type}, a -> either e a
pure = right

app : Pi {0 a b e : Type}, either e (a -> b) -> either e a -> either e b
app (right f) (right x) = right (f x)
app (right f) (left e) = left e
app (left e) x = left e

join : Pi {0 a e : Type}, either e (either e a) -> either e a
join (right x) = x
join (left e) = left e

bind : Pi {0 a b e : Type}, either e a -> (a -> either e b) -> either e b
bind (right x) f = f x
bind (left e) f = left e

