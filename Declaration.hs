module Declaration where

import Data.Set
import Data.Map as M
import Data.List as L
import Data.Maybe
import Control.Monad
import Control.Applicative hiding (Const)
import Control.Monad.State.Lazy
import Debug.Trace
import Data.Function

import Core hiding (Inductive)
import qualified Core as C
import Elaborator
import Typecheck
import Utils
import Reduction
import Substitution
import Parser
import Lexer(Loc)
import Prettyprint
import Inductive
import Equations
import Patterncheck
{-
  here we process top-level declarations
-}

type Inductive = (Loc, Name, [Param], Expr, [Ctor])
type Function = (Loc, Name, Expr, [Clause])
type CParam = (Plicity,Mult,String,Term)

data Block
  = DataBlock [Inductive]
  | FunBlock [Function]

debug = True

groupDecls :: [Decl] -> Either String [Block]
groupDecls = coupleGroups . groupBy sameDeclKind
  where
    sameDeclKind DataDecl {} DataDecl {} = True
    sameDeclKind DataDef {} DataDef {} = True
    sameDeclKind FunDecl {} FunDecl {} = True
    sameDeclKind Clause {} Clause {} = True
    sameDeclKind _ _ = False

    declName :: Decl -> String
    declName (DataDecl _ n _ _) = n
    declName (DataDef _ n _) = n
    declName (FunDecl _ n _) = n
    declName (Clause _ n _ _) = n

    declLoc :: Decl -> Loc
    declLoc (DataDecl x _ _ _) = x
    declLoc (DataDef x _ _) = x
    declLoc (FunDecl x _ _) = x
    declLoc (Clause x _ _ _) = x

    findDefs :: [Decl] -> [Decl] -> Either String [(Loc, Name, [Param], Expr, [Ctor])]
    findDefs [] [] = pure []
    findDefs (DataDef loc _ _ : _) [] = Left (show loc ++ "definition was not declared")
    findDefs defs (decl@(DataDecl loc name params arity) : decls) = case find ((name ==) . declName) defs of
      Just (DataDef _ _ ctors) -> do
        block <- findDefs (deleteBy ((==) `on` declName) decl defs) decls
        pure ((loc, name, params, arity, ctors) : block)
      Nothing -> Left (show loc ++ "declaration lacks accompanying definition")

    findClauses :: [[Decl]] -> [Decl] -> Either String [(Loc, Name, Expr, [Clause])]
    findClauses [] [] = pure []
    findClauses ((Clause loc _ _ _ : _) : _) [] = Left (show loc ++ "definition was not declared")
    findClauses clauses (decl@(FunDecl loc name ty) : decls) = case find ((name ==) . declName . head) clauses of
      Just c -> do
        let clauses' = fmap (\(Clause loc _ pats rhs) -> (loc,pats, rhs)) c
        block <- findClauses (deleteBy ((==) `on` (declName . head)) c clauses) decls
        pure ((loc, name, ty, clauses') : block)
      Nothing -> Left (show loc ++ "declaration lacks accompanying definition")

    coupleGroups :: [[Decl]] -> Either String [Block]
    coupleGroups [] = pure []
    coupleGroups (decls : defs : groups) = case (head decls, head defs) of
      (DataDecl {}, DataDef {}) -> do
        block <- findDefs defs decls
        blocks <- coupleGroups groups
        pure (Declaration.DataBlock block : blocks)
      (FunDecl {}, Clause {}) -> do
        block <- findClauses (groupBy ((==) `on` declName) defs) decls
        blocks <- coupleGroups groups
        pure (FunBlock block : blocks)
      (FunDecl loc _ _, _) -> Left (show loc ++ "declarations lacks accompanying definition")
      (DataDecl loc _ _ _, _) -> Left (show loc ++ "declarations lacks accompanying definition")
      (DataDef loc _ _, _) -> Left (show loc ++ "definitions lacks type declaration")
      (Clause loc _ _ _, _) -> Left (show loc ++ "definitions lacks type declaration")

checkBlocks :: [Block] -> ElabState -> Either String ElabState 
checkBlocks blocks st = foldM f st blocks
  where
    f st (Declaration.DataBlock defs) = checkData st defs
    f st (FunBlock defs) = checkDefinition st defs
  
checkData :: ElabState -> [Inductive] -> Either Error ElabState
checkData st defs = do 

  let defcount = length defs
      
      (def_locs, names, paramss, arities, ctors) = unzip5 defs
      
      qnames = fmap (\name -> [moduleName st, name]) names

      ctor_names = fmap (fmap fst) ctors
      
      ctor_qnames = concat (zipWith (\qname ctornames -> fmap (\name -> qname ++ [name]) ctornames) qnames ctor_names)

  mapM_ (ensureUnique st) ctor_qnames
  mapM_ (ensureUnique st) qnames

  let f :: [CParam] -> Context -> [Param] -> Either Error ([CParam],Context)
      f acc ctx ((p,m,v,ty):params) = do
        (ty,_,_) <- toEither (infer st ctx ty)
        f ((p,m,v,ty) : acc) (Hyp v ty Nothing : ctx) params
      f acc ctx [] = pure (acc,ctx)

  (paramss,ctxs) <- unzip <$> mapM (f [] []) paramss
    
  arities <- zipWithM (\ctx arity -> do
    (arity',kind,_) <- toEither (infer st ctx arity)
    ensureSort (signature st) ctx (exprLoc arity) kind
    pure arity') ctxs arities
    
  let extendArity :: Term -> [CParam] -> Term
      extendArity = L.foldl (\acc (p,m,name,ty) -> Pi p m name ty acc) 
    
      -- arities extended with parameters
      arities_ext = zipWith extendArity arities paramss
  
      -- context with extended arities
      arities_ctx = reverse (zipWith (\n t -> Hyp n t Nothing) names arities_ext)

      checkCtor :: Context -> Int -> Int -> Ctor -> Either Error Term
      checkCtor ctx defno paramno (name,expr) = do
        (t,_,_) <- toEither (infer st ctx expr)
        allOccurrencesPositive (signature st) ctx (exprLoc expr) defcount defno paramno (length ctx - defcount) (length ctx) t
        pure t
      
      checkDef :: (Int,Context,[Ctor]) -> Either Error [Term]
      checkDef (defno, ctx, ctors) = do
        mapM (checkCtor (ctx ++ arities_ctx) defno (length ctx)) ctors
    
  (ctor_tys) <- mapM checkDef (zip3 [0..] ctxs ctors)

  let fresh_id = newName st
      -- abstracted ctors explicitly quantify over the datatype parameters
      abstractCtors :: Context -> [Term] -> [Term]
      abstractCtors params ctors = fmap (flip f params) ctors where
        f = L.foldl (\acc (Hyp name ty _) -> Pi Implicit Zero name ty acc)
      
      abstracted_ctors = zipWith abstractCtors ctxs ctor_tys
      
      ctor_arities = fmap (fmap countDomains) ctor_tys -- compute arities
      
      uniparamno = 0 :: Int
      --L.foldr getUniparamno (minimum (fmap length paramss)) (concat abstracted_ctors)
  
      def_refs = fmap (\defno -> Ind fresh_id defno uniparamno) [0 .. defcount - 1]
      
      def_consts = fmap (flip App []) def_refs
  
      def_name_loc_refs = zip3 qnames def_locs def_refs
      
      ctor_instances = fmap (fmap (psubst (reverse def_consts))) abstracted_ctors
      
      ctor_refs = concat (zipWith3
        (\ctors params defno ->
          fmap
            (\ctorno ->
              Con
                fresh_id
                defno
                ctorno
                (length params))
            [0.. length ctors - 1])
        ctor_instances
        paramss
        [0..])
      
      ctor_locs = concat (fmap (fmap (exprLoc . snd)) ctors)
      
      ctor_ref_name_locs = zip3 ctor_qnames ctor_locs ctor_refs
      
      obs = signature st
      
      object = zipWith6 (\name arity ctor_names ctor_arities ctor_tys params ->
        C.Inductive {
          indName = name,
          indSort = arity,
          paramno = length params,
          introRules = zip ctor_names ctor_tys})
        names
        arities_ext
        ctor_names
        ctor_arities
        ctor_instances
        paramss
      
      name_loc_refs = ctor_ref_name_locs ++ def_name_loc_refs
      name_names = zip (concat ctor_names) ctor_qnames ++ zip names qnames
   
  when debug $ traceM (intercalate "\n" (fmap showQName qnames))
  
  pure st {
    newName = fresh_id + 1,
    internalNames = updateNameSpace name_loc_refs (internalNames st),
    signature = obs{sigInd = M.insert fresh_id object (sigInd obs)}}

checkDefinition :: ElabState -> [Function] -> Either Error ElabState
checkDefinition st defs = do
  let 
    checkSignature = fmap (\(x,_,_) -> x) . toEither . infer st []
    
    (locs, binders, tys, clausess) = unzip4 defs
    
    defcount = length defs
    
    prepareClause num ty (loc,pats,rhs) = do
        pats' <- evalStateT (checkPatterns st loc 0 pats ty) 0
        pure (Problem num [] pats' rhs)
    
    checkClauses st num clauses ty = do
      problems <- mapM (prepareClause num ty) clauses
      (ECST _ nodes bodies _) <- execStateT (compileEquations st [] [] problems ty) (ECST mempty [] [] 0)
      pure (fmap fst nodes, bodies)
    
    --(names,qnames) = unzip (fmap (\bind ->
    --  let name = binderName bind in (name, [moduleName st, name])) binders)
    
    (names,qnames) = unzip (fmap (\name -> (name, [moduleName st, name])) binders)
  
  mapM_ (ensureUnique st) qnames

  --traceM "checking signatures"

  tys <- mapM checkSignature tys

  -- insert types into context
  let
    obj_id = newName st
    obs = signature st
    alldefs = sigDef obs
    defnos = [0 .. defcount - 1]
    
    dum_heads = fmap (\n -> Ind obj_id n 0) defnos
    dum_names = updateNameSpace (zip3 qnames locs dum_heads) (internalNames st)
    dum_dats = zipWith4 C.Inductive names tys (repeat 0) (repeat [])
    dum_sig = Signature (M.insert obj_id dum_dats (sigInd obs)) alldefs
    dum_st = st {
      newName = obj_id + 1,
      internalNames = dum_names,
      signature = dum_sig}

  --traceM "checking clauses"

  (nodes,bodies) <- unzip <$> sequence (zipWith3 (checkClauses dum_st) [0..] clausess tys)
  
  --traceM $ showCaseTree (head trees)
  
  let
    computeHeight :: () -> Term -> Int -> Int
    computeHeight () (App (Def _ _ _ h) args) acc = max h (L.foldr (computeHeight ()) acc args)
    computeHeight () t acc = Utils.fold (const id) () computeHeight t acc
    
    uniparamno = 0
    
    height = 1 + maximum (concatMap (fmap (\t -> computeHeight () t 0)) bodies)
    
    new_names = updateNameSpace (zip3 qnames locs heads) (internalNames st)
    
    heads = fmap (\n -> Def obj_id n uniparamno height) defnos
  
    mkDef name ty nodes clauses = let
      
      replaceDummies () (App head args) =
        mkApp (replaceHead head) (fmap (replaceDummies ()) args)  
      replaceDummies () t = Utils.map (const id) () replaceDummies t
      
      replaceHead :: Head -> Term
      replaceHead (Ind block defno _)
        | block == obj_id = App (fromMaybe (error "bad defno") (nth defno heads)) []
      replaceHead hd = App hd []
      
      clauses' = fmap (replaceDummies ()) clauses
      
      in Definition name ty height clauses' nodes
  
    defs = zipWith4 mkDef names tys nodes bodies
    -- we still need to count height and replace dummy references
    new_sig = Signature (sigInd obs) (M.insert obj_id defs alldefs)
    
  when debug $ traceM (intercalate "\n" (fmap showQName qnames))

  pure (st {
    newName = obj_id + 1,
    internalNames = new_names,
    signature = new_sig})
