module prelude

data unit : Type where
  tt : unit

data bool : Type where
  true : bool
  false : bool

id : Pi {0 a : Type}, a -> a
id x = x

self : Pi {0 a : Type}, a -> a
self x = id (id x)

data eq {0 a:Type}(x:a): a -> Type where
  refl : eq x x

conflict : Pi {0 a : Type}, eq true false => a
conflict ()

data pair (a b : Type): Type where
  mk : a -o b -o pair a b

fst : Pi {0 a b : Type}, pair a b -> a
fst (mk x y) = x

snd : Pi {0 a b : Type}(p : pair a b), b
snd (mk x y) = y

eta : Pi {0 a b : Type}(p : pair a b), eq p (mk (fst p) (snd p))
eta (mk x y) = refl

data dpair(a : Type)(b : a -> Type): Type where
  dmk : Pi 1 x : a, b x -o dpair a b

p1 : Pi {0 a : Type}{0 b : a -> Type}, dpair a b -> a
p1 (dmk x y) = x

p2 : Pi {0 a : Type}{0 b : a -> Type}(p : dpair a b), b (p1 p)
p2 (dmk x y) = y

deta : Pi {0 a : Type}{0 b : a -> Type}(p : dpair a b), eq p (dmk (p1 p) (p2 p))
deta (dmk x y) = refl

data nat : Type where
  zero : nat
  succ : nat -> nat

data vec (a : Type): nat -> Type where
  nil : vec a zero
  cons : Pi {0 n : nat}, a -o vec a n -o vec a (succ n)

nat_rec : Pi (p : nat -> Type), p zero -> (Pi n : nat, p n -> p (succ n)) -> Pi n : nat, p n
nat_rec p pz ps zero = pz
nat_rec p pz ps (succ n) = ps n (nat_rec p pz ps n)

nat_rec_zero : Pi
  (p : nat -> Type)
  (pz : p zero)
  (ps : Pi n : nat, p n -> p (succ n)),
    eq pz (nat_rec p pz ps zero)
nat_rec_zero p pz ps = refl

nat_rec_succ : Pi
  (p : nat -> Type)
  (pz : p zero)
  (ps : Pi n : nat, p n -> p (succ n))
  (n : nat),
    eq (nat_rec p pz ps (succ n)) (ps n (nat_rec p pz ps n))
nat_rec_succ p pz ps n = refl

zip_with : Pi {0 a b c : Type}(f : a -> b -> c){0 n : nat}, vec a n -> vec b n -> vec c n
zip_with f nil nil = nil
zip_with f (cons x xs) (cons y ys) = cons (f x y) (zip_with f xs ys)

less : nat -> nat -> bool
less zero zero = false
less zero (succ _) = true
less (succ _) zero = false
less (succ n) (succ m) = less n m

