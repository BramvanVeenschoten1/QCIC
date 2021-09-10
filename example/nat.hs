module nat

import prelude
       bool

data nat : Type where
  zero : nat
  succ : nat -> nat

-- OK (oddly)
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

-- NOT OK
less : nat -> nat -> bool
less zero zero = false
less zero (succ m) = true
less (succ n) zero = false
less (succ n) (succ m) = tt --less n m
  
-- NOT OK
plus : nat -> nat -> nat
plus zero m = m
plus (succ n) m = tt -- succ (plus n m)

-- NOT OK
times : nat -> nat -> nat
times zero m = zero
times (succ n) m = succ tt -- plus m (times n m)

-- NOT OK
plus_associates : Pi (x y z : nat), prelude.eq (plus x (plus y z)) (plus (plus x y) z)
plus_associates zero y z = refl
plus_associates (succ x) y z = tt -- cong succ (plus_associates x y z)

data leq : nat -> nat -> Type where
  base : Pi {0 n : nat}, leq zero n
  step : Pi {0 n m : nat}, leq n m -> leq (succ n) (succ m)

-- OK (oddly)
leq_pred : Pi {0 n m : nat}, leq (succ n) (succ m) -> leq n m
leq_pred (step l) = l

succ_leq_zero : Pi {0 n : nat}, leq (succ n) zero -> void
succ_leq_zero ()

{-
-- error: meta variable is removed from context
leq_trans : Pi {0 x y z : nat}, leq x y -> leq y z -> leq x z
leq_trans base _ = base
leq_trans (step l1) (step l2) = step (leq_trans l1 l2) 
-}


