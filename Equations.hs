module Equations where

import Unification
import Parser
import Core
import Typecheck
import Elaborator
import Lexer(Loc)
import Reduction
import Substitution
import Utils
import Prettyprint
import Patterncheck
import Unification

import Data.Maybe
import Data.Map as M
import Data.List as L
import Control.Monad
import Control.Monad.State as C
import Debug.Trace

{-
important differences with respect to the old EC:
- the encoding and caching of problems
- the use of per-clause, partial substitutions
- ad-hoc disambiguation of singleton patterns
- reordering of pattern variables. In the original, constructor arguments are always put on top of the  
  context, but here we reorder them so the type dependencies are correct and the variables appear in the
  same order in the context as in the clause.
  Reordering has to be managed, and I think DBIs can be computed afterwards
  recall that only after splits do we get new information on which variables can be deleted.
  due to the discarding of mismatching clauses, ignore patterns and substitutions can now apply,
  so a way must be found to decide for the full context.
- outline:
  - after a split, every variable that is ignored or instantiated in *Every* clause is to be deleted,
    modulo dependencies of course.
  - ignored or implicit arguments might both need to be named if other variables depend on them,
    so the name must be distinct from the pattern. For every variable one must keep track if they
    are ignored, implicit, instantiated, split, and a (suggested) name in any case.
    deletability can just be derived from the substitution
    
    until we add @-patterns, instantiated variables can be deleted. After that, we'll keep them around
    with little issue as nothing depends on them. We can sever the connection between the named variable
    and the instantiated one.
    
    The exact representation of metas is still a question, though. We probably have to use DBLs,
    to be re-assigned after each split. This will be an interesting problem. It should then be noted
    that the encoding of problems should be independent of the numbers assigned to variables.
    
    It might actually be really easy. We a single purification with reordering and deletion, if we use
    DBLs then the resulting list is the env filter, modulo reversal and (DBI/DBL) conversion.
    
    so insert constructor arguments in context, then reorder as necessary for the instantiations to make sense.
    Thinking about replacing each instantiated variable with its later free vars, recursively.
    
    Now we must find out how to tell if a postponed substitution can be triggered. Postponedment happens iff
    some but not all clauses assigned to a branch do not have a pattern. If we pair the postponed substitution
    with the numbers of the offending clauses, we can tell when the problems have been filtered enough to
    trigger the substitutions.
    
    If an all-wildcard clause is redundant, substitution will be postponed indefinitely. To prevent this,
    it has to be triggered in the Done step.
    
    Now it seems like a good idea to do the unification of indices after filtering the clauses, so applying
    the substitutions is more straightforward.
    
    Another question arises how to properly lift variables from the fixed context afterwards.

    Interesting insight from lean: substitutions are not postponed, instead each branch is specialized and
    each rhs gets cast to it.
    
    another thing for efficient unification: discard instantiations as soon as we know the instantiated variable
    does not occur in the result.
    
    Then there is the question of whether substitutions are needed to distinguish unification state.
    the intuition is yes, as every postponement corresponds to one clauses patterns being replaced.
    
    Now for the encoding of unification states: the constraint patterns along with clause numbers can uniquely
    identify the unification states. variable, ignore and singleton patterns need not be distinguished. Once
    a variable is known to be a singleton, it will be removed. As such, the pattern code can just be either a
    list or a unit pattern.
    
    what if only clauses are shared?
    There is no duplicate work, nor risk of discrepancies with respect to the right hand side
    Env filters are applied only once. Substitutions can all just be postponed until the done clause is reached.
    How to tell which substitutions apply? during unification of indices, we know which clauses have a pattern 
    and which don't (right?) We would also rely on other machinery to recover deep defaults, which are otherwise
    lost. Then there is also the little fact that we would be doing more work if we elaborate all default
    branches separately.
    
    Anyway, one still has to wonder whether unification can be undone rather than postponed.
    
    New insight: mark postponable substitutions with defaulting clauses, as usual. This information is
    propagated inward. Caching can still be done the same way. In the done step, we know exactly which
    clauses are possible where. This information is propagated outward, as well as which substitution
    fragments are used and the disambiguated contexts. Unification can be done in the done step, as we'll
    know exactly which substitutions apply, and we also ensure each unification is performed at most
    once per clause. (modulo conflicts)
    
    for exact splits, all this ado is unnecessary, as substitutions can be applied immediately.
  
  Lean style local variables seem to be most amenable to preserve substitutions after deletion and
  reordering, but they do prompt the question of how to convert them back to DBIs. Probably,
  after sanitizing, produce an occurrence list to propagate outward, while using the re-ordered
  context locally to solve the variables.
  
  It is probably prudent to apply local visitation to the immutable context as well. Even so,
  the immutability should be preserved so that the restoration does not need to traverse the
  dag.
  
  Then there is the question of whether metavariables should carry their own types. Doing so,
  a meta might be duplicated, and if another meta in its type is instantiated, applying the subst
  will result in more work. So the answer is no.
  
  There is a tiny discrepancy, if an argument is ignored, it is to be removed from the context,
  but neither Intro nor body nodes do that..
  
  Now that DBLs are abolished, the constraints must explicitly be associated with the local variables.
  This might present a little problem with regards to the encoding of the unification state. We cannot use
  locals in the encoding, because they might be different for states we should consider equal. As such,
  the constraints must be kept in an association list.
  
  Recall that the occurence list cannot return DBIs, because it is evaluated in possibly different contexts!
  Now to figure out whether the meta's need to be pattern-coded. Consider the following problem:
  
  Nothing  Nothing  -> ..
  (Just x) (Just y) -> ..
  x        y        -> ..
  
  after splitting we get 2 default clauses with metas:
  
  0[Just 1]  2[Nothing]
  0[Nothing] 1[Just 2]
  
  the occurrence list for the default branch must contain x and y, but problem one encodes them as
  x=0, y=2
  whereas problem two encodes it as
  x=0, y=1
  
  Conclusion: metavariables must be pattern-coded
    pattern codes can be indifferent to clauses, because it does not matter from which constructor a variable
    is introduced; they either are ignored or lead to different bodies.
  
  Now for the encoding infrastructure:
    pattern codes are needed when introducing new variables, to ensure equivalence. This means that on splitting,
    the code of the scrutinee is looked up, and when introducing, the pattern depth must be found. Pattern codes
    cannot be put in the environment, as patterns can have different types. Also, the environment is reader while
    pattern codes are state. We need to lookup codes from scrutinees, as well as insert codes for fresh variables.
    this requires some kind of bimap, to be put in the state.
    
    Now, the unification state can also have a better encoding, based on the map from variables to constraints.
    
    One more thing: previous implementations removed the pattern from the constraints once it is split upon.
    Now we replace constructors by Ignore plus their variables, defaulting patterns will be left in but
    the variables are replaced by ignore patterns. This is to ensure state code consistency. The variables
    will still be deleted afterwards by context sanitization.
    => State codes should be consistent per clause, so no ignore patterns are inserted for the arguments
       of a defaulting pattern, just leave it be.
    => No Ignore patterns in place of Con patterns either
    
    The new clause code will simply be the list of variables in the constraints. The new state code must still
    distinguish clauses, otherwise 2 states resulting from a split on bool would be indistinguisable:
    
    true -> ..
    false -> ..
    
    Finally, due to first match semantics, the state code only needs the first remainging clause and its number.
    
  With the new metavariables, and the abolition of DBLs, context sanitization must now order by pattern codes.
  
  The entire EC would be simple if meta's were directly encoded as their pattern codes, but this would probably
  be more work, in addition to requiring an additional EC var in Core
  
  Interesting idea: postponement of unification in the term language can be done by introducing the equalities as
  refl patterns in constructor patterns and ignore patterns in wildcard patterns
  
  There is an optimization specificly for exact splits, if the index is a free variable, and there are no other
  variables in scope that depend on it, don't introduce an equality but perform the substitution immediately.
  
  There is some more optimization that can be done regardless of the exactness of a split. any substitution
  can be discarded if the instantiated variable does not occur in the return type.
  
  new idea: keep track of split variables for a conflict search
-}

{-
Since the final result is a list of dagnodes, the construction of this list is imperative.
Information we need to retrieve per node is the used clauses as well as used variables.
This whole thing is getting verbose, so we ought to wrap it up in a state monad.
To prevent stateful changes from leaking out of failed attempts, all recoverable errors should
use continuations. We might consider using a reader for the Elabstate, or the context, but it is unclear
whether the latter needs modification
-}



data Problem = Problem {
  problemNumber  :: Int,
  problemConstrs :: [LPattern],
  problemPats    :: [LPattern],
  problemRHS     :: Expr}

showProblem p = intercalate " "
  (fmap (showCPat . snd) (reverse (problemConstrs p)) ++
  ["|"] ++
  fmap (showCPat . snd) (problemPats p))

type PartialSubst = ([Int], Substitution)

mergeSubstitutions :: [PartialSubst] -> Substitution
mergeSubstitutions  = L.foldr (M.union . snd) mempty

type StateCode = (Int, [Int])

type Cache = Map StateCode Int

type Node = (Dag,Uses)

data ECST = ECST {
  stCache   :: Cache,
  stNodes   :: [Node],
  stClauses :: [Term],
  stNextVar :: Int}

type EC a = StateT ECST (Either String) a

type MContext = [(Int,Mult,String,Term)]

freshMeta :: EC Int
freshMeta = do
  fresh <- gets stNextVar
  modify (\st -> st {stNextVar = fresh + 1})
  pure fresh

searchDBI :: Int -> MContext -> Int
searchDBI = f 0 where 
  f _ _ [] = error "meta variable is removed from context"
  f n m ((m',_,_,_):ctx)
    | m == m' = n
    | otherwise = f (n + 1) m ctx

encodeState :: [Problem] -> StateCode
encodeState [] = error "encoding empty state"
encodeState (prob:_) = (problemNumber prob, fmap fst (problemConstrs prob))

lookupCache :: [Problem] -> EC Int -> EC Int
lookupCache probs fail = do
  cache <- gets stCache
  case M.lookup (encodeState probs) cache of
    Nothing -> fail
    Just x -> pure x

getNode :: Int -> EC Node
getNode n = gets (\nodes -> stNodes nodes !! n)

insertCache :: [Problem] -> EC Node -> EC Int
insertCache probs mnode = do
  node <- mnode
  cache <- gets stCache
  nodes <- gets stNodes
  let n = length nodes
  modify (\st -> st {
    stCache = M.insert (encodeState probs) n cache,
    stNodes = nodes ++ [node]})
  pure n

insertClause :: Term -> EC Int
insertClause body = do
  fresh <- gets (length . stClauses)
  modify (\st -> st {stClauses = stClauses st ++ [body]})
  pure fresh

namedVars :: MContext -> Problem -> [Int]
namedVars ctx = Data.Maybe.mapMaybe isRelevant . zip ctx . problemConstrs where
  isRelevant (_,(_,CIgnore)) = Nothing
  isRelevant ((meta,_,_,_),_) = Just meta

specializeContext :: [PartialSubst] -> MContext -> Term -> [Int] -> [Int] -> ([PartialSubst],MContext,[Int],Term)
specializeContext postponed ctx ty defaulting_clauses clause_vars = let
  
  (activated,postponed') = L.partition
    (\(blocking_clauses,sub) -> L.null (L.intersect blocking_clauses defaulting_clauses))
    postponed
  
  subst = mergeSubstitutions activated
  
  apply' (var,m,name,ty) = (var,m,name, applySubst subst ty)
  
  ty' = applySubst subst ty
  ctx' = zip [0..] (fmap apply' ctx)
  
  topoSort acc [] = acc
  topoSort acc ((hyp @ (dbi,(meta,m,name,ty))):ctx)
    | meta `occurs` acc = topoSort acc ctx
    | otherwise = topoSort (hyp : topoSort acc children) ctx
    where
      lookupHyp m [] = Nothing
      lookupHyp m ((hyp@(_,(m',_,_,_))):ctx)
        | m == m' = Just hyp
        | otherwise = lookupHyp m ctx
      
      occurs = (.) isJust . lookupHyp
      
      children = Data.Maybe.mapMaybe (flip lookupHyp ctx) (metaVars ty)
 
  ordered_ctx = topoSort [] (reverse ctx')
  
  filterCtx acc [] = []
  filterCtx acc ((hyp @ (dbi,(var,m,name,ty))):ctx)
    | var `elem` acc = hyp : filterCtx (L.union acc (metaVars ty)) ctx
    | otherwise = filterCtx acc ctx
  
  filtered_ctx = filterCtx (L.union clause_vars (metaVars ty')) ordered_ctx
    
  (env_filter,ctx'') = unzip filtered_ctx
  
  in (postponed',ctx'',env_filter,ty')

unvisit :: MContext -> Term -> Term
unvisit ctx = f 0 where
  f k (App head args) = App (g k head) (fmap (f k) args)
  f k t = Utils.map (const (+1)) k f t
  
  g k (Met n) = Var (k + searchDBI n ctx)
  g k hd = hd

unvisitCtx :: MContext -> Context
unvisitCtx [] = []
unvisitCtx ((meta,mult,name,ty):ctx) = Hyp name (unvisit ctx ty) Nothing : unvisitCtx ctx

showMContext :: Signature -> MContext -> String
showMContext sig ctx = showContext sig (unvisitCtx ctx)

-- TODO
-- account for constant parameters, to fix function definitions
-- add loction + function name info for stuckness?
-- construct a list of reasons for stuckness (stuck constructors, uneven clause arguments)
-- convert constraints to Ctx for printing types?
-- construct counterexample for coverage check?
-- do the whole usage checking thing
-- gather pattern codes to guide conflict search
compileEquations :: ElabState -> MContext -> [PartialSubst] -> [Problem] -> Term -> EC Int
compileEquations st ctx subst [] ty = error "coverage error should have been detected earlier"
compileEquations st ctx subst probs ty = do
  --traceM "context:"
  --traceM (showMContext (signature st) ctx)
  --traceM "problem:"
  --traceM (intercalate " " (fmap showProblem probs))

  lookupCache probs $
    insertCache probs $
    checkDone st ctx subst probs ty $
    searchSplit st ctx subst probs ty $
    tryIntro st ctx subst probs ty $
    checkAbsurd st ctx subst probs ty $
    C.lift $ Left "Equation compiler got stuck"

checkDone :: ElabState -> MContext -> [PartialSubst] -> [Problem] -> Term -> EC Node -> EC Node
checkDone st ctx subst (prob:probs) ty fail
  | L.null (problemPats prob) && all solved constrs = let
    named_vars = namedVars ctx prob
    (_,ctx',env_filter,ty') = specializeContext subst ctx ty [problemNumber prob] named_vars
    constrs' = applyFilter env_filter constrs
    ctx'' = zipWith applyName ctx constrs'
    ctx''' = unvisitCtx ctx''
    ty'' = unvisit ctx'' ty
    in do
      --traceM "Done, new context:"
      --traceM $ showContext (signature st) ctx'''
    
      (body,uses) <- C.lift (check st ctx''' (problemRHS prob) ty'')
      target <- insertClause body
    -- finally, a dbi useenv has to be converted to an meta useenv
      pure (Body target env_filter, uses)
  | otherwise = fail
  where
    solved (_,CCon {}) = False
    solved (_,CAbsurd _) = False
    solved _ = True
    
    constrs = problemConstrs prob
    
    applyName (meta,mult,name,ty) (_,CVar loc name') = (meta,mult,name',ty)
    applyName hyp _ = hyp
    

searchSplit :: ElabState -> MContext -> [PartialSubst] -> [Problem] -> Term -> EC Node -> EC Node
searchSplit st ctx subst probs @ (prob:_) ty fail = let
  findConPat (_,(_,CCon {})) = True
  findConPat _ = False

  pat_metas = fmap fst (L.filter findConPat (zip [0..] (problemConstrs prob)))

  in L.foldr (trySplit st ctx subst probs ty) fail pat_metas

checkAbsurd :: ElabState -> MContext -> [PartialSubst] -> [Problem] -> Term -> EC Node -> EC Node
checkAbsurd st ctx subst probs @ (prob:_) ty fail = case problemConstrs prob of
  ((_,CAbsurd _):_) -> trySplit st ctx subst probs ty 0 fail
  _ -> fail
    
trySplit :: ElabState -> MContext -> [PartialSubst] -> [Problem] -> Term -> Int -> EC Node -> EC Node
trySplit st ctx postponed probs ty scrut_dbi fail = let
  (scrut_met,scrut_mult,_,scrut_ty) = ctx !! scrut_dbi
  App (Ind block defno _) args = scrut_ty
  sig = signature st
  ind = sigInd sig ! block !! defno
  pno = paramno ind
  (params,indices) = L.splitAt pno args
  ctors = introRules ind
  ctor_tys = fmap (instantiateCtor params . snd) ctors
  ctor_count = length ctors
  tags = [0 .. ctor_count - 1]
  
  isDefaulting p = case problemConstrs p !! scrut_dbi of
    (_,CCon {}) -> Nothing
    _ -> Just (problemNumber p)
  
  defaulting_clauses = Data.Maybe.mapMaybe isDefaulting probs 
  
  isStuck (Stuck _,_,_) = True
  isStuck _ = False
  
  partitionProblem ctor_arity tag prob = let
    constrs = problemConstrs prob
    (shallow,scrut_pat : deep) = L.splitAt scrut_dbi constrs
    in case scrut_pat of
      (_,CCon loc tag' args) ->
        if tag == tag'
        then Just (False,prob {problemConstrs = reverse args ++ shallow ++ (0,CIgnore) : deep})
        else Nothing
      (_,CAbsurd _) -> Nothing
      _ -> Just (True,prob {problemConstrs = replicate ctor_arity (0,CIgnore) ++ constrs})
  
  tryUnify :: Int -> Term -> EC (Result,MContext,[Problem])
  tryUnify tag ctor_ty = do
    let ctor_arity = countDomains ctor_ty
    metas <- sequence (replicate ctor_arity freshMeta)
    let
      args' = fmap (flip App [] . Met) metas
    
      probs' = Data.Maybe.mapMaybe (partitionProblem ctor_arity tag) probs

      introArgs :: MContext -> [Int] -> Term -> (MContext,Term)
      introArgs acc [] ty = (acc,ty)
      introArgs acc (arg:args) (Pi p m name src dst) =
        introArgs ((arg,times scrut_mult m,"?X" ++ show arg,src):acc) args (psubst [App (Met arg) []] dst)
      
      (arg_ctx, App _ ty_args) = introArgs [] metas ctor_ty
            
      indices' = L.drop pno ty_args
      
      applied_ctor = App (Con block defno tag pno) (params ++ args')
      scrut_term = App (Met scrut_met) []
      
      equations = zip indices indices' ++ [(scrut_term,applied_ctor)]
      
      base = mergeSubstitutions postponed

      unify_result
        | L.null probs' = unifyIndices (signature st) base mempty equations
        | all fst probs' = Yes mempty
        | otherwise = unifyIndices (signature st) base mempty equations
    pure (unify_result, arg_ctx, fmap snd probs')
  
  checkCoverage (No,_,_) = pure (-1,[])
  checkCoverage (Yes _,_,[]) =
    -- provide location and counterexample
    C.lift $ Left "clauses do not cover all possible inputs"
  checkCoverage (Yes subst, arg_tys, probs) = compileBranch subst arg_tys probs
  
  compileBranch :: Substitution -> MContext -> [Problem] -> EC (Int,[Int])
  compileBranch subst arg_tys probs = let
    
    postponed' = (defaulting_clauses,subst) : postponed
    
    (before,after) = L.splitAt scrut_dbi ctx
    ctx_with_args = before ++ arg_tys ++ after
    
    named_vars = L.foldr (L.union . namedVars ctx_with_args) mempty probs
    
    (postponed'',ctx',env_filter,ty') =
      specializeContext
        postponed'
        ctx_with_args
        ty
        defaulting_clauses
        named_vars
    
    probs' = fmap (\prob -> prob {
      problemConstrs = applyFilter env_filter (problemConstrs prob)}) probs
    
    in do
      --traceM "named vars"
      --traceM $ show named_vars
    
      target <- compileEquations st ctx' postponed'' probs' ty'
      -- do multiplicity checks
      pure (target, env_filter)
  
  in do
    unification_results <- zipWithM tryUnify tags ctor_tys
    if any isStuck unification_results
    then fail
    else do
      --traceM $ "split on " ++ show scrut_dbi
      branches <- mapM checkCoverage unification_results
      pure (Case scrut_dbi branches, error "implement usage propagation")

-- distinguisth `done` from `stuck`
tryIntro :: ElabState -> MContext -> [PartialSubst] -> [Problem] -> Term -> EC Node -> EC Node
tryIntro st ctx subst probs ty fail = do
  --traceM "intro"
  case whnf (signature st) [] ty of
    Pi p m name src dst ->
      if  any (L.null . problemPats) probs
      then fail
      else do
        meta <- freshMeta
        let
          explicitIntro prob = let
            (pat:pats) = problemPats prob
            constrs = problemConstrs prob
            in prob {
              problemConstrs = pat : constrs,
              problemPats = pats}
          probs' = fmap explicitIntro probs
          
          name'
            | L.null name = "?X" ++ show meta
            | otherwise = name
          ctx' = (meta,m,name',src) : ctx
        target <- compileEquations st ctx' subst probs' (psubst [App (Met meta) []] dst)
        node <- getNode target
        let use : uses = snd node
        
        -- add a location from any variable pattern, otherwise it does not matter
        -- TODO C.lift (checkUse name m use)
        pure (Intro target,uses)
    _ -> fail -- impossible?
