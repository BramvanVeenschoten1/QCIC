module nat

import prelude
       bool

data nat : Type where
  zero : nat
  succ : nat -> nat

nat_rec : Pi (p : nat -> Type), p zero -> (Pi n : nat, p n -> p (succ n)) -> Pi n : nat, p n
nat_rec p pz ps zero = pz
nat_rec p pz ps (succ n) = ps n (nat_rec p pz ps n)

nat_rec_zero : Pi
  (p : nat -> Type)
  (pz : p zero)
  (ps : Pi n : nat, p n -> p (succ n)),
    prelude.eq pz (nat_rec p pz ps zero)
nat_rec_zero p pz ps = refl

nat_rec_succ : Pi
  (p : nat -> Type)
  (pz : p zero)
  (ps : Pi n : nat, p n -> p (succ n))
  (n : nat),
    prelude.eq (nat_rec p pz ps (succ n)) (ps n (nat_rec p pz ps n))
nat_rec_succ p pz ps n = refl

leq : nat -> nat -> bool
leq zero _ = true
leq (succ n) zero = false
leq (succ n) (succ m) = leq n m

less : nat -> nat -> bool
less n m = leq (succ n) m

plus : nat -> nat -> nat
plus zero m = m
plus (succ n) m = succ (plus n m)

times : nat -> nat -> nat
times zero m = zero
times (succ n) m = plus m (times n m)

plus_associates : Pi (x y z : nat), prelude.eq (plus x (plus y z)) (plus (plus x y) z)
plus_associates zero y z = refl
plus_associates (succ x) y z = cong succ (plus_associates x y z)

data Leq : nat -> nat -> Type where
  base : Pi {0 n : nat}, Leq zero n
  step : Pi {0 n m : nat}, Leq n m -> Leq (succ n) (succ m)

is_prop : Pi {0 n m : nat}(l1 l2 : Leq n m), prelude.eq l1 l2
is_prop base base = refl
is_prop (step l1) (step l2) = cong step (is_prop l1 l2)

leq_refl : Pi (0 n : nat), Leq n n
leq_refl zero = base
leq_refl (succ n) = step (leq_refl n)

leq_pred : Pi {0 n m : nat}, Leq (succ n) (succ m) -> Leq n m
leq_pred (step l) = l

leq_trans : Pi {0 x y z : nat}, Leq x y -> Leq y z -> Leq x z
leq_trans base _ = base
leq_trans (step l1) (step l2) = step (leq_trans l1 l2) 

Less : nat -> nat -> Type
Less n m = Leq (succ n) m

less_than_succ : Pi {0 n : nat}, Less n zero -> void
less_than_succ ()

strong : Pi (p : nat -> Type)
            (h : Pi 0 x : nat, (Pi 0 y : nat, Less y x => p y) -> p x)
            (n : nat)
            (0 m : nat),
              Less m n => p m
strong p h zero m l = absurd (less_than_succ l)
strong p h (succ n) m l1 = h m (\j l2, strong p h n j (leq_trans l2 (leq_pred l1)))

left_dec : Pi (n m : nat), lift (leq n m) -> Leq n m
left_dec zero m refl = base
left_dec (succ _) zero ()
left_dec (succ n) (succ m) l = step (left_dec n m l)

right_dec : Pi {0 n m : nat}, Leq n m -> lift (leq n m)
right_dec base = refl
right_dec (step l) = right_dec l

