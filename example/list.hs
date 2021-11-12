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

reverse2 : Pi {0 a : Type}, list a -> list a
reverse2 nil = nil
reverse2 (cons x xs) = append (reverse2 xs) (cons x nil)

lemma0 : Pi {0 a : Type}(xs ys : list a)(P : list a -> Type), P (reverse2 (append xs ys)) -> P (append (reverse2 ys) (reverse2 xs))
lemma0 nil ys P = subst P (nil_left_id (reverse2 ys))
lemma0 (cons x xs) ys P pf =
  let xn : list a = cons x nil in
  let revxs : list a = reverse2 xs in
  let revys : list a = reverse2 ys in
  let ih = lemma0 xs ys in
  let pf2 : P (append (reverse2 (append xs ys)) xn) = pf in
  let pf3 : P (append (append revys revxs) xn) = ih (\zs, P (append zs xn)) pf2 in
  let pf4 : P (append revys (append revxs xn)) = subst P (sym (append_associative revys revxs xn)) pf3 in
    pf4

reverse_append : Pi {0 a : Type}(xs ys : list a), prelude.eq (reverse2 (append xs ys)) (append (reverse2 ys) (reverse2 xs))
reverse_append xs ys = lemma0 xs ys (prelude.eq (reverse2 (append xs ys))) refl

map_composition : Pi {0 a b c : Type}(f : b -> c)(g : a -> b)(xs : list a), prelude.eq (map (comp f g) xs) (map f (map g xs))
map_composition f g nil = refl
map_composition f g (cons x xs) = cong (cons (f (g x))) (map_composition f g xs)


