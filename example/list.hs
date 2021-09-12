module list

import prelude
       function
       nat
       bool
       monoid
       pair

data list (a : Type): Type where
  nil : list a
  cons : a -> list a -> list a

foldl : Pi {0 a b : Type}, (a -> b -> b) -> b -> list a -> b
foldl f acc nil = acc
foldl f acc (cons x xs) = foldl f (f x acc) xs

foldr : Pi {0 a b : Type}, (a -> b -> b) -> b -> list a -> b
foldr f acc nil = acc
foldr f acc (cons x xs) = f x (foldr f acc xs)

append : Pi {0 a : Type}, list a -> list a -> list a
append xs ys = foldr cons ys xs

reverse : Pi {0 a : Type}, list a -> list a
reverse = foldl cons nil

map : Pi {0 a b : Type}, (a -> b) -> list a -> list b
map f = foldr (comp cons f) nil

filter_aux : Pi {0 a : Type}, bool -> (list a -> list a) -> list a -> list a
filter_aux true = id
filter_aux false = const id

filter : Pi {0 a : Type}, (a -> bool) -> list a -> list a
filter f nil = nil
filter f (cons x xs) = filter_aux (f x) (cons x) (filter f xs)

partition_aux : Pi {0 a : Type}, a -> bool -> pair (list a) (list a) -> pair (list a) (list a)
partition_aux x true  (mk xs ys) = pair.pair.mk (cons x xs) ys
partition_aux y false (mk xs ys) = pair.pair.mk xs (cons y ys)

partition : Pi {0 a : Type}, (a -> bool) -> list a -> pair (list a) (list a)
partition f nil = pair.pair.mk nil nil
partition f (cons x xs) = partition_aux x (f x) (partition f xs)

pure : Pi {0 a : Type}, a -> list a
pure x = cons x nil

join : Pi {0 a : Type}, list (list a) -> list a
join = foldr append nil

app : Pi {0 a b : Type}, list (a -> b) -> list a -> list b
app fs xs =
  let f : (a -> b) -> list b = flip map xs
  in foldr (comp append f) nil fs

bind : Pi {0 a b : Type}, list a -> (a -> list b) -> list b
bind xs f = foldr (comp append f) nil xs

length : Pi {0 a : Type}, list a -> nat
length = foldr (const succ) zero

nth : Pi {0 a : Type}(n : nat)(xs : list a), prelude.eq true (less n (length xs)) => a
nth zero nil ()
nth zero (cons x xs) _ = x
nth (succ n) nil ()
nth (succ n) (cons x xs) l = nth n xs l

append_associative : Pi {0 a : Type}(x y z : list a), prelude.eq (append x (append y z)) (append (append x y) z)
append_associative nil ys zs = refl
append_associative (cons x xs) ys zs = cong (cons x) (append_associative xs ys zs)

nil_left_id : Pi {0 a : Type}(xs : list a), prelude.eq xs (append xs nil)
nil_left_id nil = refl
nil_left_id (cons x xs) = cong (cons x) (nil_left_id xs)

nil_right_id : Pi {0 a : Type}(xs : list a), prelude.eq xs (append nil xs)
nil_right_id xs = refl

list_monoid : Pi {0 a : Type}, monoid (list a)
list_monoid =
  monoid.monoid.mk
    nil
    append
    nil_left_id
    nil_right_id
    append_associative


