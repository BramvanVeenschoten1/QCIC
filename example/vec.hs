module vec

import prelude
       nat

data fin : nat -> Type where
  fzero : Pi {0 n : nat}, fin (succ n)
  fsucc : Pi {0 n : nat}, fin n -> fin (succ n)

data vec (a : Type): nat -> Type where
  nil : vec a zero
  cons : Pi {0 n : nat}, a -o vec a n -o vec a (succ n)

{-
-- for some reason, expected type is (vec a (?X4 m)) where n = succ ?X4
-- this is an error in the unification of the equation compiler
append : Pi {0 a : Type}{0 n m : nat}, vec a n -> vec a m -> vec a (plus n m)
append nil ys = ys
append (cons x xs) ys = cons x (append xs ys)
-}

-- OK (oddly)
zip_with : Pi {0 a b c : Type}(f : a -> b -> c){0 n : nat}, vec a n -> vec b n -> vec c n
zip_with f nil nil = nil
zip_with f (cons x xs) (cons y ys) = cons (f x y) (zip_with f xs ys)

-- OK (oddly)
nth : Pi {0 a : Type}{0 n : nat}, fin n -> vec a n -> a
nth fzero (cons x xs) = x
nth (fsucc i) (cons x xs) = nth i xs
