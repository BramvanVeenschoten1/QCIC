module Unification where

import Core
import Reduction
import Substitution
import Utils

import Data.Map

type Equation = (Term,Term)

data Result
  = Yes Substitution
  | No
  | Stuck Equation

{-
  something has come up: equalities between a pair of fully applied contructors, for which the injectivity rule applies,
  may still be depended upon. consider example:
  
  x y : nat
  i : fin (succ x)
  j : fin (succ y)
  e : eq (mk (succ x) i) (mk (succ y) j)
  
  applying injectivity will yield the problem:
  
  x y : nat
  i : fin (succ x)
  j : fin (succ y)
  e1 : eq (succ x) (succ y)
  e2 : eq (subst fin e1 i) j
  
  here we have the option of applying injectivity again on e1, but in this case e2 depends on it.
  we can use injectivity, but keep e1 in scope. Then, use K to solve for e1:
    
    [e1 injective]
    x y : nat
    i : fin (succ x)
    j : fin (succ y)
    e1 : eq (succ x) (succ y)
    e3 : eq x y
    e2 : eq (subst fin e1 i) j
    [solve y]
    x : nat
    i j : fin (succ x)
    e1 : eq (succ x) (succ x)
    e2 : eq (subst fin e1 i) j
    [delete e1]
    x : nat
    i j : fin (succ x)
    e2 : eq i j
    
  the question is whether the use of K is necessary here- manual unification reveals it is not,
  which prompts the question on how to do it systematically.
  The answer is likely hidden in the implementation details of the injectivity proof,
  it might need the dummy projections in the motive or something alike.
  projections in the motive are exactly what we need.
  
  The procedure has to be modified, as injectivity is no longer an independent step when the equality is depended upon.
  
  Things get even more complicated if we have equations of the form (eq (x,z) (y,z)) where x can be instantiated by y but
  the equation (z=z) has to be deleted by K.
  
  Thus we can distinguish 3 different cases:
  1. The equality is not depended upon. we can just remove it and add the injections to the telescope for further unification.
  2. The equality is depended upon, and needs K to self-unifyIndices. We add the injections to the telescope like in step 1, but keep the
     equality around, to be deleted by K in the next step
  3. The equality is depended upon, but does not need K to self-unifyIndices. The same procedure as in (2) can be used, but
     a single J application will suffice. In this case, we need to replace the variables in the motive by projections,
     which use the default variables that are in scope
  
  Recal that the unification steps are as follows:
  1. solution
  2. deletion (requires K)
  3. conflict (simplest of all)
  4. injectivity
  Now with three interesting subcases:
     4.1. independent
     4.2. self-unifying with K, turns into 4.1 + 2
     4.3. self-unifying without K, turns into 1 with a special motive
  
  Defining the motive for 4.3 is the hard part, where the sub-variables of the term
  have to be defined as projections of the parameter of J
  
  recall that for an equality
  (x y : a)
  (e : eq x y)
  and motive P,
  the branch will be checked as (P x refl) and the whole term as (P y e).
  P y e is the type before the solution, and P x refl after.
  So in the motive P, every subterm of y must be replaced by a proper projection on z.
  Each projection could have the subterms of either x or y as default branches, it does not seem to matter as of now
  
  But wait, there is more:
  
  e : (x, true) = (false, y)
  
  How?
  Also solved, see Documents/J_action2.lean
  Just introduce the equalities in terms of the projections of the motive argument.
  These equalities can be ommitted if their free variables do not occur in the J parameter
  
  note: Recall that in using J, the parameter is the instantiating value and the index is the
  instantiated variable. For the injectivity step, variables that occur in the parameter might
  be instantiated. This will be forgotten if their equalities are not introduced. variables in the
  index will all be instantiated, be it by constructors or parameter variables. This is all quite
  complex, as before an injection step can be done, the terms must suffer some exploratory unification
  to find the instantiated parameters. The question remains whether all equalities can be introduced instead.
  
  to summmarize:
  have terms
  T0 T1 : a
  e : T0 = T1
  
  where T0 and T1 are unifiable through solution and injectivity, and e is depended on later.
  We  use J on e with a motive:
  
  P = fun t e' -> T'
  
  Recall that t is instantiated with T0 in the branch (the unified context) and by T1 in
  the parent context. In the branch, we want equalities between the free variables of T0 and
  their correspondent values in T1. in the parent context, these can be provided as reflexivities.
  Thus T' abstracts over these equalites, each of which is stated in terms of
  a projection of t and the corresponding subterm of T1. Then, each occurrence of a free variable from T1 is
  replaced by the corresponding projection of t. Finally, each occurrence of e is replaced by e'.
  Care has to be taken that if an injection of (T0 = T1) yields (x = y), y is instantiated and the equation can be deleted.
  
  It appears we are doing too much work, as it seems each injection has to be unified recursively before the motive
  can be created. Investigate if dependent injection can be reduce to a single step again.
  It appears to work fine, though equalities where the rhs is a variable in T1 appear to become redundant.
  
  New procedure:
  
  given a problem (e : T0 = T1) where e is depended upon, use J with parameter T0 and index T1 and motive P where
  P = fun t e' -> T'
  introduce injective equalities, with on the left the subterms of T1 and on the right side the projections of t.
  replace every occurrence of e by e'. replace every dependent occurrence of T1 by t. This prompts one more question: how? The goal is merely to remove the dependency on e.
  
  naive procedure: replace every occurrence by fresh variables, solve variables by unification, so using e' will
  solve the correct ones. after solving, instantiate all remaining free variables with T1.
  
  This discussion is put on hold for now. All this trouble is not needed if we can freely use K.
  
  Finally, there is still the problem of not allowing equalities on types. No equality between types ever results
  from injectivity, so thankfully this is an entirely separate matter. For uniform parameters this is not an issue.
  For non-uniform parameters, its better to just derive their case functions, abstracting over the proper motive
  and branches. But this prompts the question: does this break termination checks?
-}

unifyIndices :: Signature -> Substitution -> Substitution -> [Equation] -> Result
unifyIndices sig base subst [] = Yes subst
unifyIndices sig base subst (eq : eqs)
  | canDelete = unifyIndices sig base subst eqs
  | otherwise = tryConflictInjectSolveCycle 
  where
    subst' = union base subst
    l  = whnf sig [] (applySubst subst' (fst eq))
    r  = whnf sig [] (applySubst subst' (snd eq))
    eq' = (l,r)
    
    canDelete :: Bool
    canDelete = convertible sig [] True l r
    
    tryConflictInjectSolveCycle :: Result
    tryConflictInjectSolveCycle =
      case (l,r) of
        (App (Con _ _ c0 _) xs0, App (Con _ _ c1 _) xs1)
                            -> injectOrConflict c0 c1 xs0 xs1
        (App (Met n) [], t) -> cycleOrSolve n t
        (t, App (Met n) []) -> cycleOrSolve n t
        _                   -> Stuck eq'

    injectOrConflict :: Int -> Int -> [Term] -> [Term] -> Result
    injectOrConflict c0 c1 xs0 xs1
      | c0 == c1 = inject xs0 xs1
      | otherwise = No

    inject :: [Term] -> [Term] -> Result
    inject xs0 xs1 =
      unifyIndices sig base subst (zip xs0 xs1 ++ eqs) 
    
    -- check if reducing terms is useful
    cycleOrSolve :: Int -> Term -> Result
    cycleOrSolve n t
      | not (occursMet n t) = unifyIndices sig base (Data.Map.insert n t subst) eqs
      | headOccurs n t      = No
      | otherwise           = Stuck eq'
    
    headOccurs :: Int -> Term -> Bool
    headOccurs n (App (Met m) _)
      | n == m = True
    headOccurs n (App (Con _ _ _ _) xs) = any (headOccurs n) xs
    headOccurs _ _ = False
  
