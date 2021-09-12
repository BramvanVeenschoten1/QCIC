module vec

import prelude
       nat

data fin : nat -> Type where
  fzero : Pi {0 n : nat}, fin (succ n)
  fsucc : Pi {0 n : nat}, fin n -> fin (succ n)

data vec (a : Type): nat -> Type where
  nil : vec a zero
  cons : Pi {0 n : nat}, a -o vec a n -o vec a (succ n)

append : Pi {0 a : Type}{0 n m : nat}, vec a n -> vec a m -> vec a (plus n m)
append nil ys = ys
append (cons x xs) ys = cons x (append xs ys)

map : Pi {0 a b : Type}(f : a -> b){0 n : nat}, vec a n -> vec b n
map f nil = nil
map f (cons x xs) = cons (f x) (map f xs)

replicate : Pi {0 a : Type}(n : nat), a -> vec a n
replicate zero x = nil
replicate (succ n) x = cons x (replicate n x)

app : Pi {0 a b : Type}{0 n : nat}, vec (a -> b) n -> vec a n -> vec b n
app nil nil = nil
app (cons f fs) (cons x xs) = cons (f x) (app fs xs)

zip_with : Pi {0 a b c : Type}(f : a -> b -> c){0 n : nat}, vec a n -> vec b n -> vec c n
zip_with f nil nil = nil
zip_with f (cons x xs) (cons y ys) = cons (f x y) (zip_with f xs ys)

nth : Pi {0 a : Type}{0 n : nat}, fin n -> vec a n -> a
nth fzero (cons x xs) = x
nth (fsucc i) (cons x xs) = nth i xs
