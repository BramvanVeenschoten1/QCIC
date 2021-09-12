module russels

import prelude
       dpair

data M : Type where
  mkm : Pi I : Type, (I -> M) -> M

mk2 : Pi (0 a : Type)(0 b : a -> Type)(x : a), b x -> dpair a b
mk2 a b x y = mk x y

elem : M -> M -> Type
elem e (mkm I f) = dpair I (\i, eq e (f i))

not_in_self : M -> Type
not_in_self = \x, not (elem x x)

R : M
R = mkm (dpair M (\x, not (elem x x))) p1

lemma1 : Pi (x : M), elem x R -> not_in_self x
lemma1 x (mk (mk y yny) refl) = yny

lemma2 : Pi (x : M), not_in_self x -> elem x R
lemma2 x xnx = mk (mk2 M not_in_self x xnx) refl

lemma3 : not_in_self R
lemma3 rnr = lemma1 R rnr rnr

lemma4 : elem R R
lemma4 = lemma2 R lemma3

contradiction : void
contradiction = lemma3 lemma4
