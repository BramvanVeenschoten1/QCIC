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

-- TODO
-- give implicit arguments usable names, take care not to shadow any variables
-- also, top-level implicit arguments might unintendedly shadow variable patterns
-- make visual representation for case dags
-- account for constant parameters, to fix function definitions
-- add loction + function name info for stuckness?
-- construct a list of reasons for stuckness (stuck constructors, uneven clause arguments)
-- convert constraints to Ctx for printing types?
-- construct counterexample for coverage check?
-- do the whole usage checking thing
-- gather pattern codes to guide conflict search

data Problem = Problem {
  problemNumber  :: Int,
  problemConstrs :: [CPattern],
  problemSubst   :: Substitution,
  problemPats    :: [CPattern],
  problemRHS     :: Expr}

showProblem p = intercalate " "
  (fmap showCPat (reverse (problemConstrs p)) ++
  ["|"] ++
  fmap showCPat (problemPats p))

data ECST = ECST {
  stClauses :: Map Int Term,
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
  f _ m [] = error ("meta variable " ++ show m ++ " is removed from context")
  f n m ((m',_,_,_):ctx)
    | m == m' = n
    | otherwise = f (n + 1) m ctx

namedVars :: MContext -> [CPattern] -> [Int]
namedVars ctx = Data.Maybe.mapMaybe isRelevant . zip ctx where
  isRelevant (_,CIgnore) = Nothing
  isRelevant ((meta,_,_,_),_) = Just meta

specializeContext :: MContext -> Substitution -> Term -> Int -> [Int] -> (MContext,[Int],Term)
specializeContext ctx subst ty clause clause_vars = let
  
  applyHyp (var,m,name,ty) = (var,m,name, applySubst subst ty)
  
  ty' = applySubst subst ty
  ctx' = zip [0..] (fmap applyHyp ctx)
  
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
  
  in --trace
      -- ("ty vars: " ++ show (metaVars ty') ++ "\nkept vars: " ++ show (fmap (\(x,_,_,_) -> x) ctx''))
       (ctx'',env_filter,ty')

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

compileEquations :: ElabState -> MContext -> [Problem] -> Term -> EC Tree
compileEquations st ctx [] ty = C.lift (Left "clauses do not cover all possible inputs")
  -- present possible arguments that are not covered
compileEquations st ctx probs ty = do
  --traceM "context:"
  --traceM (showMContext (signature st) ctx)
  --traceM "problem:"
  --traceM (intercalate " " (fmap showProblem probs))
  checkDone st ctx probs ty $
    searchSplit st ctx probs ty $
    tryIntro st ctx probs ty $
    checkAbsurd st ctx probs ty $
    C.lift $ Left "Equation compiler got stuck"

-- give an MContext with multiplicities, so they can be checked here.
-- there is no need to do this in the case tree
-- here is also the only use for variable pattern locations
compileRHS :: ElabState -> MContext -> Int -> Expr -> Term -> EC ()
compileRHS st ctx clause rhs ty = do
  clauses <- gets stClauses
  unless (clause `member` clauses) $ do
    let ty' = unvisit ctx ty
        ctx' = unvisitCtx ctx
    (body,uses) <- C.lift (check st ctx' rhs ty')
    -- check multiplicities
    modify (\st -> st {stClauses = M.insert clause body clauses})

checkDone :: ElabState -> MContext -> [Problem] -> Term -> EC Tree -> EC Tree
checkDone st ctx (Problem num constrs subst pats rhs:_) ty fail

  | L.null pats && all solved constrs = let
    named_vars = namedVars ctx constrs
    (ctx',env_filter,ty') = specializeContext ctx subst ty num named_vars
    constrs' = applyFilter env_filter constrs
    ctx'' = zipWith applyName ctx' constrs'
    
    in do
      --traceM "done"
      traceM "\nDone, old context:"
      traceM $ showContext (signature st) (unvisitCtx ctx)
      --traceM "named metas:"
      --traceM $ show named_vars
      --traceM "env filter:"
      --traceM $ show env_filter
      traceM "new context:"
      traceM $ showContext (signature st) (unvisitCtx ctx'')
      
      compileRHS st ctx'' num rhs ty'
      pure (Body num env_filter)
  | otherwise = fail
  where
    solved (CCon {}) = False
    solved (CAbsurd _) = False
    solved    _ = True
    
    applyName (meta,mult,name,ty) (CVar loc name') = (meta,mult,name',ty)
    applyName hyp _ = hyp


searchSplit :: ElabState -> MContext -> [Problem] -> Term -> EC Tree -> EC Tree
searchSplit st ctx probs @ (prob:_) ty fail = let
  findConPat (_,CCon {}) = True
  findConPat _ = False

  pat_metas = fmap fst (L.filter findConPat (zip [0..] (problemConstrs prob)))

  in L.foldr (trySplit st ctx probs ty) fail pat_metas

checkAbsurd :: ElabState -> MContext -> [Problem] -> Term -> EC Tree -> EC Tree
checkAbsurd st ctx probs @ (prob:_) ty fail = case problemConstrs prob of
  (CAbsurd _:_) -> trySplit st ctx probs ty 0 fail
  _ -> fail


isStuck :: Result -> Bool
isStuck (Stuck _) = True
isStuck _ = False

partitionProblem :: Substitution -> Int -> Int -> Int -> Problem -> Maybe Problem
partitionProblem subst scrut_dbi ctor_arity tag prob = let
  constrs = problemConstrs prob
  (shallow,scrut_pat : deep) = L.splitAt scrut_dbi constrs
  in case scrut_pat of
    CCon loc tag' args ->
      if tag == tag'
      then Just (prob {
        problemConstrs = reverse args ++ shallow ++ CIgnore : deep,
        problemSubst = M.union subst (problemSubst prob)})
      else Nothing
    CAbsurd _ -> Nothing
    _ -> Just (prob {problemConstrs = replicate ctor_arity CIgnore ++ constrs})
  
introArgs :: Mult -> MContext -> [Int] -> Term -> (MContext,Term)
introArgs m acc [] ty = (acc,ty)
introArgs m acc (arg:args) (Pi p m' name src dst) =
  introArgs m ((arg,times m m',"?X" ++ show arg,src):acc) args (psubst [App (Met arg) []] dst)


-- initial unification should be performed with the substitution of the first clause
-- the new substitution must be applied to all non-defaulting clauses
-- care must be taken, however, that names given to the tree are unique with respect to ALL clauses
trySplit :: ElabState -> MContext -> [Problem] -> Term -> Int -> EC Tree -> EC Tree
trySplit st ctx probs ty scrut_dbi fail = do
  metas' <- mapM (flip replicateM freshMeta) ctor_arities
  let unification_results = zipWith3 tryUnify tags metas' ctor_tys
  if any (isStuck . fst) unification_results
  then fail
  else trace str $ Case scrut_dbi <$> zipWithM compileBranch tags unification_results
  where
    (scrut_met,scrut_mult,_,scrut_ty) = ctx !! scrut_dbi
    App (Ind block defno _) args = whnf sig [] scrut_ty
    sig = signature st
    ind = sigInd sig ! block !! defno
    pno = paramno ind
    (params,indices) = L.splitAt pno args
    ctors = introRules ind
    ctor_tys = fmap (instantiateCtor params . snd) ctors
    ctor_arities = fmap countDomains ctor_tys
    tags = [0 .. ]
    subst = problemSubst (head probs)
    
    str = "params: " ++ intercalate ", " (fmap (showTerm (signature st) []) params)
    
    tryUnify :: Int -> [Int] -> Term -> (Result,MContext)
    tryUnify tag metas ctor_ty = (unify_result, arg_ctx) where
        args' = fmap (flip App [] . Met) metas
          -- here, we should give a suitable name for the variable. Think of the Pi's name, or x, 
          -- suffixed with a number to make it distinct from existing variables
        
        (arg_ctx, full_ty) = introArgs scrut_mult [] metas ctor_ty
        
        App hd ty_args = full_ty
        
        indices' = L.drop pno ty_args
        
        applied_ctor = App (Con block defno tag pno) (params ++ args')
        scrut_term = App (Met scrut_met) []
        
        equations = zip indices indices' ++ [(scrut_term,applied_ctor)]

        str = "unify indices:\ntype 1:\n" ++
          showTerm sig [] (App hd (params ++ indices)) ++
          "\ntype 2:\n" ++
          showTerm sig [] (App hd (params ++ indices')) ++
          "\nequations:\n" ++
          intercalate ", " (fmap (\(l,r) ->
            showTerm sig [] l ++
            " = " ++
            showTerm sig [] r) equations) ++
          "\n"
        
        sig = signature st

        unify_result = unifyIndices (signature st) subst mempty equations

    
    compileBranch tag (No,_) = pure ([], Case 0 [])
    compileBranch tag (Yes subst', arg_tys) =
      (,) arg_names <$> compileEquations st ctx' probs' ty where
        ctor_arity = ctor_arities !! tag
        probs' = Data.Maybe.mapMaybe (partitionProblem subst' scrut_dbi ctor_arity tag) probs
        
        ctx' = arg_tys ++ ctx
        
        sig = signature st
        
        str = showSubst sig [] subst ++ "\n\n" ++ showSubst sig [] subst'
        
        arg_names = fmap (\(_,_,x,_) -> x) arg_tys

      --traceM "named vars"
      --traceM $ show named_vars
    
    -- check singleton criterion

-- distinguisth `done` from `stuck`
tryIntro :: ElabState -> MContext -> [Problem] -> Term -> EC Tree -> EC Tree
tryIntro st ctx probs ty fail = do
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
        tree <- compileEquations st ctx' probs' (psubst [App (Met meta) []] dst)
        
        -- add a location from any variable pattern, otherwise it does not matter
        pure (Intro "" tree)
    _ -> fail -- impossible?
