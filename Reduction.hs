module Reduction where

import Data.Map
import Data.List(lookup,intercalate, elemIndex,foldl)
import Data.Maybe
import Data.Function
import Core
import Substitution
import Utils
import Debug.Trace
import Prettyprint
import Data.List as L

{- here we evalutate terms and test their equality -}

-- le nouveaux: 
{-
NOTE: by the reduction semantics of the casetrees, environment filters
list their arguments from least DBI (head of the env) to greatest

- casetrees are now casedags, and their evaluation requires the nodelist
- env-filters now apply

- a question arises on whether we use substitutions in the reduction engines.
- substitutions are used in both the lhs' and rhs'. In spine-local inference, the elaborator
  can apply substitutions before checking conversion, so it is not strictly necessary.
  In unification, the instantiation of the context and every other equations may be tricky.
  As such, it is probably simpler to keep substitutions in the reducer
  none of the above is true. reduction will not substitute metavariables

- environments need to be added
-}

--unwind (Config k e t s) = mkApp (psubst (fmap unwind e) t) (fmap (\(p,t) -> (p, unwind t)) s)
unwind e t s = mkApp (psubst e t) s
unwind' e t s = mkApp (psubst e (App t [])) s

reduce :: Signature -> Context -> Int -> Term -> (Term,Bool)
reduce sig ctx delta' t = beta 0 [] t [] where

  beta :: Int -> [Term] -> Term -> [Term] -> (Term,Bool)
  beta k e (Let _ _ x y) s =
    beta (k + 1) (fst (beta k e x []) : e) y s
  beta k e (Lam _ _ _ _ dst) (x:s) =
    beta (k + 1) (x : e) dst s
  beta k e (App head args) s =
    delta k e head (fmap (\arg -> fst (beta k e arg [])) args ++ s)
  beta k e t s = (unwind e t s, True)
  
  delta :: Int -> [Term] -> Head -> [Term] -> (Term,Bool)
  delta k e t @ (Var n) s
    | n < k = beta 0 [] (fromMaybe (error "bad dbi") (nth n e)) s
    | otherwise = case nth (n - k) ctx >>= hypValue of
      Just x -> beta 0 [] (Substitution.lift (n - k + 1) x) s
      Nothing -> (unwind' e t s, True)
  delta k e t @ (Def block defno _ height) s
    | delta' >= height = (unwind' e t s, False)
    | otherwise =
      let
        def = fromMaybe (error "bad defno") (nth defno (sigDef sig ! block))
        clauses = defClauses def
        nodes = defNodes def
        first = last nodes
        fail = (unwind' e t s, True)
      in --trace "delta" $
         iota nodes clauses fail [] first s
  delta k e t s = (unwind' e t s, True)
  
  iota :: [Dag] -> [Term] -> (Term,Bool) -> [Term] -> Dag -> [Term] -> (Term,Bool)
  iota nodes clauses fail e (Intro t) (x:s) =
    --trace "intro" $
    iota nodes clauses fail (x:e) (fromMaybe (error "bad node index") (nth t nodes)) s
  iota nodes clauses fail e (Body target env_filter) s = let
    e' = applyFilter env_filter e
    k = length e'
    t = fromMaybe (error "clauses out of bounds") (nth target clauses)
    in
     -- trace "body" $
      beta k e' t s
  iota nodes clauses fail e (Case n alts) s = case whnf sig ctx <$> nth n e of
    Nothing -> fail
    Just (App (Con _ _ ctorno paramno) args) -> let
      args' = reverse (Prelude.drop paramno args)
      e'    = args' ++ e
      (target_tag,env_filter) = fromMaybe (error "bad ctorno in case") (nth ctorno alts)
      target_node =  fromMaybe (error "bad node index") (nth target_tag nodes)
      e'' = applyFilter env_filter e'
      in 
        --trace "case" $
        iota nodes clauses fail e'' target_node s
    _ -> fail
  iota _ _ fail _ _ _ =
   -- trace "fail" $
    fail

whnf sig ctx = fst . reduce sig ctx 0

convertible :: Signature -> Context -> Bool -> Term -> Term -> Bool
convertible sig ctx flag t0 t1 = alpha ctx flag t0 t1 || machine flag (beta t0) (beta t1) where
  
  -- it appears the context can be removed from alpha here
  alpha ctx flag Type Type = True
  alpha ctx flag Kind Kind = True
  alpha ctx flag (Lam _ _ name src0 dst0) (Lam _ _ _ _ dst1) =
    convertible sig (Hyp name src0 Nothing : ctx) flag dst0 dst1
  alpha ctx flag (Pi _ m0 name src0 dst0) (Pi _ m1 _ src1 dst1) =
    (m0 == m1 || not flag && m1 == Many) &&
    convertible sig ctx flag src1 src0 &&
    convertible sig (Hyp name src0 Nothing : ctx) flag dst0 dst1
  alpha ctx flag (Let name ta0 a0 b0) (Let _ ta1 a1 b1) =
    convertible sig ctx True ta0 ta1 &&
    convertible sig ctx True a0 a1 &&
    convertible sig (Hyp name ta0 (Just a0) : ctx) flag b0 b1
  alpha ctx flag (App f0 xs0) (App f1 xs1) =
    f0 == f1 && and (zipWith (alpha ctx True) xs0 xs1)
  alpha ctx flag t0 t1 = False
  
  beta :: Term -> (Term,Bool)
  beta = reduce sig ctx maxBound
  
  deltaStep flag (m0 @ (t0, norm0)) (m1 @ (t1, norm1)) = let
    heightOf (App (Def _ _ _ h) _) = h
    heightOf _ = 0
  
    h0 = heightOf t0
    h1 = heightOf t1
    
    delta
      | norm0     = h1 - 1
      | norm1     = h0 - 1
      | h0 == h1  = max 0 (h0 - 1)
      | otherwise = min h0 h1
      
    m0' = reduce sig ctx delta t0
    m1' = reduce sig ctx delta t1
    
    proceed
      | norm0     = machine flag m0  m1'
      | norm1     = machine flag m0' m1
      | otherwise = machine flag m0' m1'
    in proceed
  
  machine flag m0 @ (t0, norm0) m1 @ (t1, norm1) =
    alpha ctx flag t0 t1 || not (norm0 && norm1) && deltaStep flag m0 m1
