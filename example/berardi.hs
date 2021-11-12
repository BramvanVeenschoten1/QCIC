module berardi

import prelude
       function
       either
       bool

data retract (a b : Type): Type where
  mkr : Pi (i : a -> b)
           (j : b -> a),
           (Pi x : a, prelude.eq (j (i x)) x) ->
             retract a b

data retract_cond (a b : Type): Type where
  mkc : Pi (i : a -> b)
           (j : b -> a),
           (retract a b -> Pi x : a, prelude.eq (j (i x)) x) ->
             retract_cond a b

trivial_retract : Pi {0 a : Type}, retract a a
trivial_retract = mkr id id (\x, refl)

trivial_retract_cond : Pi {0 a : Type}, retract_cond a a
trivial_retract_cond = mkc id id (\r x, refl)

i2 : Pi {0 a b : Type}, retract_cond a b -> a -> b
i2 (mkc i j inv) = i

j2 : Pi {0 a b : Type}, retract_cond a b -> b -> a
j2 (mkc i j inv) = j

inv2 : Pi {0 a b : Type}(rc : retract_cond a b)(x : retract a b)(x : a), prelude.eq (j2 rc (i2 rc x)) x
inv2 (mkc i j inv) = inv

Pow : Type -> Type
Pow p = p -> bool

U : Type
U = Pi p : Type, Pow p

PU : Type
PU = Pow U

decide_retract : Pi {0 a b : Type}, decidable (retract (Pow a) (Pow b)) -> retract_cond (Pow a) (Pow b)
decide_retract (left (mkr f g e)) = mkc f g (\x, e)
decide_retract (right nr) = mkc (\x y, false) (\x y, false) (\r, absurd (nr r))

dec_is_empty : Pi {0 p : Type}, decidable p -> bool
dec_is_empty (left _) = false
dec_is_empty (right _) = true

dec_p_is_not_empty : Pi {0 p : Type}(dp : decidable p)(x : p), prelude.eq (dec_is_empty dp ) false
dec_p_is_not_empty (left x) y  = refl
dec_p_is_not_empty (right x) y  = absurd (x y)

dec_not_p_is_not_empty : Pi {0 p : Type}(dp : decidable p)(x : prelude.not p), prelude.eq (dec_is_empty dp ) true
dec_not_p_is_not_empty (left x) y = absurd (y x)
dec_not_p_is_not_empty (right x) y = refl

subst2 : Pi {0 a : Type}(0 x y : a)(p : a -> Type), prelude.eq x y -> p x -> p y
subst2 x y p e px = subst p e px

not_lem : prelude.not (Pi 0 p : Type, decidable p)
not_lem LEM =
  let Lemma1 : Pi (0 a b : Type), retract_cond (Pow a) (Pow b) = \a b, decide_retract (LEM (retract (Pow a) (Pow b)))
  in let Psi : Pi X : Type, PU -> Pow X =
    \X, j2 (Lemma1 X U)
  in let Phi : Pi X : Type, Pow X -> PU =
    \X, i2 (Lemma1 X U)
  in let projU : U -> PU = \u, u U
  in let injU : PU -> U = \h X, Psi X (Phi U h)
  in let Lemma2 : Pi f : PU, prelude.eq (projU (injU f)) f =
    \f, inv2 trivial_retract_cond trivial_retract f
  in let PU_retracts_U : retract PU U = mkr injU projU Lemma2
  in let elem : U -> U -> Type = \u v, lift (projU v u)
  in let is_empty : Type => bool = \p, dec_is_empty (LEM p) 
  in let p_is_not_empty : Pi {0 p : Type}(x : p), prelude.eq (is_empty p) false =
    \x, dec_p_is_not_empty (LEM p) x
  in let not_p_is_not_empty : Pi {0 p : Type}(x : prelude.not p), prelude.eq (is_empty p) true =
    \x, dec_not_p_is_not_empty (LEM p) x
  in let not_in_self : U -> bool = \u, is_empty (elem u u)
  in let r : U = injU not_in_self
  in let Lemma3 : elem r r -> void =
    \rinr,
      let T1 : prelude.eq (not_in_self r) true =
        subst2 (projU (injU not_in_self)) not_in_self (\f, prelude.eq (f r) true) (Lemma2 not_in_self) rinr
      in let T2 : prelude.eq (not_in_self r) false =
        p_is_not_empty rinr
      in conflict (trans (sym T2) T1)
  in let Lemma4 : prelude.not (elem r r) -> void =
    \notrinr,
      let T0 : prelude.not (prelude.eq (projU (injU not_in_self) r) true) = notrinr
      in let T1 : prelude.not (prelude.eq (not_in_self r) true) =
        subst2 (projU (injU not_in_self)) not_in_self (\f, prelude.not (prelude.eq (f r) true)) (Lemma2 not_in_self) T0
      in let T2 : prelude.eq (not_in_self r) true =
        not_p_is_not_empty notrinr
      in T1 T2
  in either_case Lemma3 Lemma4 (LEM (elem r r))

  

