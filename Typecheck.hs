module Typecheck where

import Core
import Substitution
import Reduction
import Elaborator
import Lexer(Loc)
import Parser
import Prettyprint
import Utils

import Debug.Trace
import Data.Maybe
import Data.Map as M  hiding ((\\))
import Data.Either
import Data.List as L
import Control.Monad

{- TODO
- give location of arguments in case of unification failure
- give location and value of spine in case of inference failure
- give location for unused linear arguments
- fix unification, definitions are expanded too eagerly
  with f : a -> b = x = g x x
    ?M x = f x should result in ?M = f, but f gets expanded into g x x
    ?M x = g x x
    and gets stuck
- implement multiplicity checks for implicit functions
  - requires multiplicity gathering for complete terms
  - might as well separate mult checking from spine inference
-}

type Postponed = ([Int], Int, Mult, Term, Expr) -- blocking variables, instantiating variable, mult, type, expression

type Use = [(Loc,Mult)]

type Uses = [Use]

noUses :: Uses
noUses = repeat []

singleUse :: Int -> Loc ->  Uses
singleUse n loc = replicate n [] ++ [(loc,One)] : noUses

multiplyUses :: Mult -> Uses -> Uses
multiplyUses Zero = const noUses
multiplyUses One  = id
multiplyUses Many = fmap (fmap (\(loc,m) -> (loc, times Many m)))

addUses :: Uses -> Uses -> Uses
addUses = zipWith (++)

useSum :: Use -> Mult
useSum = L.foldl (\acc (loc,m) -> plus acc m) Zero

data InferResult a
  = Success a
  | TypeError String
  | InferenceFailure String

instance Functor InferResult where
  fmap f (Success x) = Success (f x)
  fmap f (TypeError e) = TypeError e
  fmap f (InferenceFailure e) = InferenceFailure e

instance Applicative InferResult where
  pure = Success
  
  Success f <*> Success x = Success (f x)
  Success _ <*> TypeError e = TypeError e
  Success _ <*> InferenceFailure e = InferenceFailure e
  TypeError e <*> _ = TypeError e
  InferenceFailure e <*> _ = InferenceFailure e

instance Monad InferResult where
  return = pure
  
  Success x >>= f = f x
  TypeError e >>= _ = TypeError e
  InferenceFailure e >>= _ = InferenceFailure e

fromEither :: Either String a -> InferResult a
fromEither (Right x) = pure x
fromEither (Left e) = TypeError e

toEither :: InferResult a -> Either String a
toEither (Success x) = pure x
toEither (InferenceFailure e) = Left e
toEither (TypeError e) = Left e

typeOfHead :: Signature -> Context -> Head -> Term
typeOfHead sig ctx t = case t of
  Met n -> error "type of meta"
  Var n -> lift (n + 1) (hypType (fromMaybe (error "TypeOfHead: Var out of range") (nth n ctx)))
  Ind i j _ -> indSort (fromMaybe (error $ "bad ind defno: " ++ show j) (nth j (sigInd sig ! i)))
  Con i j k _ -> snd (introRules (sigInd sig ! i !! j) !! k)
  Def i j _ _ -> defType ((sigDef sig ! i) !! j)

typeOf :: Signature -> Context -> Term -> Term
typeOf sig ctx = f where
  f (App head tail)   = h (typeOfHead sig ctx head) tail
  f (Pi p m name src dst) = typeOf sig (Hyp name src Nothing : ctx) dst
  f (Lam p m name src dst) = Pi p m name src (typeOf sig (Hyp name src Nothing : ctx) dst)
  f (Let name ty val body) = psubst [val] (typeOf sig (Hyp name ty (Just val) : ctx) body)
  -- type of var
  
  h ty [] = ty
  h (Pi p m name src dst) (arg : args) = h (whnf sig ctx (psubst [arg] dst)) args

-- look up a qualified name in the symbol table
lookupQualified :: ElabState -> Loc -> QName -> InferResult (Term,Term,Uses)
lookupQualified st loc qname =
  case lookupQName qname st of
    Nothing -> TypeError (show loc ++ "unknown name: " ++ showQName qname)
    Just (_,ref) -> Success (App ref [], typeOfHead
      (signature st)
      (error "typeOfHead on qualified names should not inspect context")
      ref, noUses)

-- look up a name in the symbol table and lookup Unqualified if appropriate
lookupUnqualified :: ElabState -> Loc -> Name -> InferResult (Term,Term,Uses)
lookupUnqualified st loc name = let
  in case lookupName name st of
    Nothing      -> TypeError (show loc ++ "\nunbound variable: " ++ name)
    Just [qname] -> lookupQualified st loc qname
    Just xs      -> TypeError (show loc ++ "\nambiguous name: " ++ name)

-- lookup a name in the context and return appropriate uses if present
lookupCtx :: Context -> Loc -> Name -> Maybe (InferResult (Term,Term,Uses))
lookupCtx ctx loc name = f 0 ctx where
  f n [] = Nothing
  f n ((Hyp name1 ty _):hyps)
    | name == name1 = Just (Success (App (Var n) [], lift (n + 1) ty, singleUse n loc))
    | otherwise     = f (n + 1) hyps

inferHead :: ElabState -> Context -> EHead -> InferResult (Term,Term,Uses)
inferHead st ctx head = case head of
  EName loc xs -> lookupQualified st loc xs
  EVar  loc x -> fromMaybe (lookupUnqualified st loc x) (lookupCtx ctx loc x)

ensureSort :: Signature -> Context -> Loc -> Term -> Either String ()
ensureSort sig ctx loc t = case whnf sig ctx t of
  Type -> pure ()
  Kind -> pure ()
  other -> Left (
    show loc ++
    "\nexpected some sort, but got\n" ++
    showTerm sig ctx other)

letAux :: ElabState -> Context -> Expr -> Maybe Expr -> Either String (Term,Term,Uses)
letAux st ctx expr ty = case ty of
  Just ty -> do
    let ty_loc = exprLoc ty
    (ty,k,_) <- toEither (infer st ctx ty)
    ensureSort (signature st) ctx ty_loc k
    (term,uses) <- check st ctx expr ty
    pure (term,ty,uses)
  Nothing -> toEither (infer st ctx expr)

-- restore location for unused linears
checkUse :: String -> Mult -> Use -> Either String ()
checkUse name Zero [] = pure ()
checkUse name Zero ((loc,_):_) = Left (show loc ++ "relevant use of erased variable `" ++ name ++ "`")
checkUse name One [] = Left ("linear variable `" ++ name ++ "` is unused")
checkUse name One [(loc,One)] = pure ()
checkUse name One [(loc,Many)] = Left (show loc ++ "linear variable `" ++ name ++ "` is used in unrestricted context")
checkUse name One ((loc,_):_) = Left (show loc ++ "multiple uses of linear variable `" ++ name ++ "`")
checkUse _ _ _ = pure ()

lamAux :: ElabState -> Context -> Loc -> Loc -> String -> Expr -> Term -> Either String (Term,Uses)
lamAux st ctx loc nloc name body ty = case whnf (signature st) ctx ty of
  Pi Implicit m name src dst -> do
    (body',uses) <- lamAux st (Hyp name src Nothing : ctx) loc nloc name body dst
    let (use:uses') = uses
    checkUse name m use
    pure (Lam Implicit m name src body', uses')
  Pi Explicit m _ src dst -> do
    (body',uses) <- check st (Hyp name src Nothing : ctx) body dst
    let (use:uses') = uses
    checkUse name m use
    pure (Lam Explicit m name src body', uses')    
  other -> Left (show loc ++
    "\bexpected a term of type\n" ++
    showTerm (signature st) ctx other ++
    "\nbut got a lambda expression")

-- change to either, as this inference failure is not recoverable
check :: ElabState -> Context -> Expr -> Term -> Either String (Term,Uses)
check st ctx expr ty = case expr of
  EType loc -> Left (show loc ++ "\nType may never occur in head position")
  ELam loc nloc name body -> lamAux st ctx loc nloc name body ty
  EApply loc head args -> do
    (hd,hd_ty,hd_uses) <- toEither (inferHead st ctx head)
    (app,app_ty,uses,menv,subst,postponed) <- eatSpine st ctx loc hd hd_ty hd_uses args mempty mempty mempty
    subst' <- unify (exprLoc expr) (signature st) menv 0 ctx subst app_ty ty
    (subst'',uses') <- toEither (solvePostponed st ctx menv subst' postponed uses)
    let app' = applySubst subst'' app
    if Prelude.null (keys menv \\ keys subst'')
    then pure ()
    else Left (show loc ++ "not all metas were solved")
    pure (app',uses')
  ELet loc nloc name annot val body -> do
    (val,val_ty,val_uses) <- letAux st ctx val annot
    (body,uses) <- check st (Hyp name val_ty (Just val) : ctx) body (lift 1 ty)
    let (use : uses') = uses
    pure (Let name val_ty val body, addUses uses' (multiplyUses (useSum use) val_uses))
  pi @ EPi {} -> do
    let sig = signature st
        loc = exprLoc pi
    (ty1,k,uses) <- toEither (infer st ctx pi)
    if convertible sig ctx True ty k
    then pure (ty1,uses)
    else Left (
      show loc ++
      "\nin context\n" ++
      showContext sig ctx ++
      "\nexpected a term of type\n" ++
      showTerm sig ctx ty ++
      "\nbut got a dependent function type\n" ++
      showTerm sig ctx ty1)
  
{-
    let loc = exprLoc other
        sig = signature st
    (term, ty1, uses) <- infer st ctx other
    if convertible sig ctx False ty ty1
    then pure (term,uses)
    else TypeError (
      show loc ++
      "\nin context:" ++
      showContext sig ctx ++ 
      "\nterm:\n" ++
      showTerm sig ctx term ++
      "\nhas type:\n" ++
      showTerm sig ctx ty1 ++
      "\nbut expected type:\n" ++
      showTerm sig ctx ty ++
      "\nreduced:\n"++
      showTerm sig ctx (whnf sig ctx ty) ++
      "\n<=/=>\n" ++
      showTerm sig ctx (whnf sig ctx ty1))
-}

infer :: ElabState -> Context -> Expr -> InferResult (Term,Term,Uses)
infer st ctx expr = case expr of
  EType loc -> pure (Type, Kind, noUses)
  EApply loc head args -> do
    (hd,hd_ty,hd_uses) <- inferHead st ctx head
    (term,ty,uses,menv,subst,postponed) <- fromEither (eatSpine st ctx loc hd hd_ty hd_uses args mempty mempty mempty)
    (subst',uses') <- solvePostponed st ctx menv subst postponed uses
    let term' = applySubst subst' term
        ty' = applySubst subst' ty
    if Prelude.null (keys menv \\ keys subst')
    then pure ()
    else InferenceFailure (show loc ++ "not all metas were solved")
    pure (term',ty',uses')
  EPi loc p m name src dst -> do
    let src_loc = exprLoc src
        dst_loc = exprLoc dst
    (src,src_k,src_uses) <- infer st ctx src
    fromEither (ensureSort (signature st) ctx src_loc src_k)
    (dst,dst_k,dst_uses) <- infer st (Hyp name src Nothing:ctx) dst
    fromEither (ensureSort (signature st) ctx dst_loc dst_k)
    pure (Pi p m name src dst, dst_k, addUses src_uses dst_uses)
  ELet loc nloc name ty val body -> do
    (val, val_ty, val_uses) <- fromEither (letAux st ctx val ty)
    (body,ty,uses) <- infer st (Hyp name val_ty (Just val) : ctx) body
    let (use:uses') = uses
    pure (Let name val_ty val body, psubst [val] ty, addUses uses' (multiplyUses (useSum use) val_uses))
  ELam loc _ _ _ -> InferenceFailure (show loc ++
    "\ntype of function cannot be inferred")

eatSpine :: ElabState -> Context -> Loc -> Term -> Term -> Uses ->
  [(Plicity,Expr)] ->
  MetaEnv ->
  Substitution ->
  [Postponed] ->
  Either String (Term,Term,Uses,MetaEnv,Substitution,[Postponed])
eatSpine st ctx loc head head_ty head_uses args menv subst postponed = do
  let head_ty' = whnf (signature st) ctx (applySubst subst head_ty)
  --traceM ("> " ++ showTerm (signature st) ctx (applySubst subst head_ty'))
  case head_ty' of
    Pi Implicit Zero name src dst -> let
      v = size menv
      fresh = App (Met v) []
      menv' = M.insert v src menv
      in
        eatSpine st ctx loc
          (mkApp head [fresh])
          (psubst [fresh] dst)
          head_uses args menv' subst postponed
    Pi Implicit _ _ _ _ -> Left (show loc ++
      "\nimplicit function has non-zero multiplicity")
      -- we can do a little better than this. every meta-variable occurs exactly once in the spine,
      -- so once solved, gather uses from the values and add those instead
    Pi Explicit m name src dst -> case args of
      [] -> pure (head,head_ty,head_uses,menv,subst,postponed)
      ((_,arg):args) -> let src_metas = metaVars src; arg_loc = exprLoc arg in
        if Prelude.null src_metas
        then do
          (arg,arg_uses) <- check st ctx arg src
          eatSpine st ctx loc
            (mkApp head [arg])
            (psubst [arg] dst)
            (addUses head_uses (multiplyUses m arg_uses))
            args menv subst postponed
        else case infer st ctx arg of
          Success (arg,arg_ty,arg_uses) -> do
            subst' <- unify arg_loc (signature st) menv 0 ctx subst src arg_ty
            eatSpine st ctx loc
              (mkApp head [arg])
              (psubst [arg] dst)
              (addUses head_uses (multiplyUses m arg_uses))
              args menv subst' postponed
          InferenceFailure e -> let
            v = size menv
            fresh = App (Met v) []
            menv' = M.insert v src menv
            in eatSpine st ctx loc
                 (mkApp head [fresh])
                 (psubst [fresh] dst)
                 head_uses args menv' subst
                 ((src_metas,v,m,src,arg) : postponed)
          TypeError e -> Left e
    other ->
      if Prelude.null args
      then pure (head,head_ty,head_uses,menv,subst,postponed)
      else Left (show loc ++
        "\nin context:\n" ++
        showContext (signature st) ctx ++
        "\nexpected a function, but the term\n" ++
        showTerm (signature st) ctx head ++
        "\nhas type\n" ++
        showTerm (signature st) ctx other)

-- TODO: a conflict should have the location of the argument, expected type, given type, and unification failure
-- Q: Should unify have recoverable failures? (such as for (?M x = x))
unify :: Loc -> Signature -> MetaEnv -> Int -> Context -> Substitution -> Term -> Term -> Either String Substitution
unify loc sig menv k ctx subst t0 t1 = cmp subst (whnf sig ctx t0) (whnf sig ctx t1) where

  cmp subst t0 t1 = case (t0,t1) of
    (Type,Type) -> pure subst
    (Kind,Kind) -> pure subst  
    (Lam _ _ name src0 dst0, Lam _ _ _ _ dst1) ->
      unify' (k + 1) (Hyp name src0 Nothing : ctx) subst dst0 dst1
    (Pi _ m0 name src0 dst0, Pi _ m1 _ src1 dst1) -> do
      assert (m0 == m1)
      subst' <- unify' k ctx subst src0 src1
      unify' (k + 1) (Hyp name src0 Nothing : ctx) subst' dst0 dst1
    (Let name ta0 a0 b0, Let _ ta1 a1 b1) -> do
      subst' <- unify' k ctx subst ta0 ta1
      subst2 <- unify' k ctx subst' a0 a1
      unify' (k + 1) (Hyp name ta0 (Just a0) : ctx) subst2 b0 b1
    (App (Met v) [], val) -> case M.lookup v subst of
      Just x -> cmp subst (lift k x) val
      Nothing -> let
        impossible = error "bad occurs check in unify"
        subst' = M.insert v (psubst (replicate k impossible) val) subst    
        in do
          let l_ty = applySubst subst (lift k (menv ! v))
              r_ty = typeOf sig ctx val
          assert (doesNotOccur ctx 0 (k-1) val)  
          assert (convertible sig ctx True
            (applySubst subst (lift k (menv ! v)))
            (typeOf sig ctx val))
          pure subst'
    (App (Met v) xs0, App f1 xs1) -> case M.lookup v subst of
      Just val -> cmp subst (mkApp (lift k val) xs0) (App f1 xs1)
      Nothing -> let
        len0 = length xs0
        len1 = length xs1
        (left,right) = L.splitAt (len1 - len0) xs1
        val = App f1 left
        impossible = error "bad occurs check in unify"
        subst' = M.insert v (psubst (replicate k impossible) val) subst    
        in do
          let l_ty = applySubst subst (lift k (menv ! v))
              r_ty = typeOf sig ctx val
          assert (len0 <= len1)
          assert (doesNotOccur ctx 0 (k-1) val)
          --traceM "types:"
          --traceM (showTerm sig ctx l_ty)
          --traceM (showTerm sig ctx r_ty)
          
          -- one more thing, we must assert the term instantiating the meta
          -- is closed modulo the meta-context, and then must be lifted accordingly
          -- 1. carry the difference between the local context and the spine context
          -- 2. assert no references to the local context exist
             -- equal to k is ok, free but smaller is problematic
             -- doesNotOccur should be usable here
             -- we need an inclusive range, any free variable up to but not including k is
             -- prohibited, so we assert doesNotOccur ctx 0 (k - 1)
          -- 3. antilift (?) the term. basically, substitute with error
          
          assert (convertible sig ctx True
            (applySubst subst (lift k (menv ! v)))
            (typeOf sig ctx val))
          foldM (uncurry . cmp) subst' (zip xs0 right)
    (App f0 xs0, App f1 xs1) -> do
      assert (f0 == f1)
      foldM (uncurry . cmp) subst (zip xs0 xs1)
    (t0, t1) -> err
    where
      unify' = unify loc sig menv
    
      err = Left (show loc ++
        "\nin context:\n" ++
        showContext sig ctx ++
        "\nwith metas:\n" ++
        showMetaEnv sig ctx menv ++
        "\nand substitution:\n" ++
        showSubst sig ctx subst ++
        "\ntype mismatch, couldn't unify\n" ++
        showTerm sig ctx t0 ++
        "\nwith\n" ++
        showTerm sig ctx t1)
      
      assert b = if b then pure () else err

solvePostponed :: ElabState -> Context -> MetaEnv -> Substitution -> [Postponed] -> Uses -> InferResult (Substitution,Uses)
solvePostponed st ctx env subst postponed uses
  | Prelude.null postponed = pure (subst,uses)
  | Prelude.null retries =
    InferenceFailure "total inference failure, implement location please"
    -- it seems the best error is to give the maximal application, showing which metas can't be inferred
  | otherwise = do
      (subst',uses') <- foldM retry (subst,uses) retries
      solvePostponed st ctx env subst' postponed' uses'
  where
    solved_metas = keys subst
    
    isReady (vars,_,_,_,_) = all (`elem` solved_metas) vars
    
    (retries,postponed') = L.partition isReady postponed
    
    retry (subst,uses) (_,var,m,ty,expr) = do
      let ty' = applySubst subst ty
      (term,uses') <- fromEither (check st ctx expr ty')
      let subst' = M.insert var term subst
      pure (subst', addUses uses (multiplyUses m uses'))

        
