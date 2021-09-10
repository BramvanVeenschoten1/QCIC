module list

import prelude
       function
       nat

data list (a : Type): Type where
  nil : list a
  cons : a -> list a -> list a

-- OK (oddly)
foldl : Pi {0 a b : Type}, (a -> b -> b) -> b -> list a -> b
foldl f acc nil = acc
foldl f acc (cons x xs) = foldl f (f x acc) xs

-- OK (oddly)
foldr : Pi {0 a b : Type}, (a -> b -> b) -> b -> list a -> b
foldr f acc nil = acc
foldr f acc (cons x xs) = f x (foldr f acc xs)

append : Pi {0 a : Type}, list a -> list a -> list a
append xs ys = foldr cons ys xs

reverse : Pi {0 a : Type}, list a -> list a
reverse = foldl cons nil

map : Pi {0 a b : Type}, (a -> b) -> list a -> list b
map f = foldr (comp cons f) nil

pure : Pi {0 a : Type}, a -> list a
pure x = cons x nil

join : Pi {0 a : Type}, list (list a) -> list a
join = foldr append nil

app : Pi {0 a b : Type}, list (a -> b) -> list a -> list b
app fs xs = foldr (comp append (the ((a -> b) -> list b) (flip map xs))) nil fs

bind : Pi {0 a b : Type}, list a -> (a -> list b) -> list b
bind xs f = foldr (comp append f) nil xs

length : Pi {0 a : Type}, list a -> nat
length = foldr (const succ) zero

{-
-- again, meta variable removed from context
nth : Pi {0 a : Type}(n : nat)(xs : list a), eq true (less n (length xs)) => a
nth zero nil ()
nth zero (cons x xs) _ = x
nth (succ n) nil ()
nth (succ n) (cons x xs) l = nth n xs l
-}
