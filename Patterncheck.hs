module Patterncheck where

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

import Data.Maybe
import Data.Map as M
import Data.List as L
import Control.Monad
import Control.Monad.State as C
import Debug.Trace

-- the disambiguation of patterns, pattern coding of metavariables, typechecking of patterns, even the compilation
-- of the RHS can all be done before splitting/trying to find the covering. The patterns cannot entirely be compiled
-- to core terms, as core does not have Absurd, Ignore or Var, but constructor heads can be inserted.
-- advantages are:
--   tree-builder does not need to manage label variable codes
--   pre-checked patterns rule out stuck patterns in the tree builder
--   pre-checked clause lengths rule out stuck lambdas
--   pre-checked clause might report large eliminations early
--   might give the dag builder more flexibility to determine optimal split order
--   clean separation between coverage checker and type checker
-- disatvantages:
--   unification has to be performed twice, once during type checking and once during coverage checking
--   (also illustrates the need for forced patterns)
-- The pattern type checker would also have to:
--   introduce implicits
--   postone unification problems, such as (not (not b) = b, b = true)
--   safely postponing unification problems might require typed unification, which can be done same as in old times
--   the procedure would be similar to solving constraints in the type inference engine, a stuck equation would
--   list blocking variables, which when solved triggers a retry.
-- how would it work when compiling to terms? Not much difference it seems.
-- we can also settle for not completely type checking the patterns. We would introduce implicits,
--   check belonging and arity of constructors, compute the metavariable codes, but leave out unification and RHS checking
--   This still means that unification of types is not supported, just like right now
--   either way, we can dispense with occurrence lists, as we can simply take the union of variables of the clauses of the
--   current problem.
-- it occurs to me now that lean checks the RHS' before building the casetree, and passes the RHS' to the tree builder
--   as arguments to allow defaulting clauses to forget their unification states. This does not solve the work duplication
--   problem though, as defaulting clauses still perform full unification, and the result is a tree, not a dag
-- disambiguated patterns will have disambiguated variables as either nullary constructors or variables
{-
procedure:
-- check clause length
-- insert implicit arguments
-- recursively check patterns

-- just in: constructor types have to be instantiated with their parameters to get their argument types correct
-- but we were going to skip (non-uniform) parameters anyway in introducing arguments.

-- we might as well keep track of where we are in terms of pattern codes

-- we can even produce the MetaEnv, but it might be less work to do it later

-- we might as well invert the pattern codes, as they will not be used to look anything up.

-- we don't need pattern codes to compute dbis from metas, but we might need a context list of sorts.
-- which we'll need to modify with care

-- take care not to shadow variables by naming implicit constructor arguments.
-- implicit function arguments are fine, though.

clauses need only take an equal number of arguments modulo absurdity, though.
-}

type LPattern = (Int,CPattern)

data CPattern
  = CIgnore                      --     
  | CAbsurd Loc                  -- loc
  | CVar    Loc String           -- loc, name
  | CCon    Loc Int [LPattern] -- loc, tag, args

type PC a = StateT Int (Either String) a

showCPat :: CPattern -> String
showCPat CIgnore = "_"
showCPat (CAbsurd _) = "()"
showCPat (CVar _ s) = s
showCPat (CCon _ tag []) = "c" ++ show tag
showCPat (CCon _ tag pats) = "(c" ++ show tag ++ " " ++ intercalate " " (fmap (showCPat . snd) pats) ++ ")"

newLabel :: PC Int
newLabel = do
  fresh <- get
  modify (+1)
  pure fresh

-- give some meaningful location?
checkPatterns :: ElabState -> Loc -> Int -> [Pattern] -> Term -> PC [LPattern]
checkPatterns st loc depth pats ty =
  case whnf (signature st) [] ty of
    Pi Implicit m name src dst -> do
      label <- newLabel
      pats' <- checkPatterns st loc (depth + 1) pats dst
      pure ((label,CIgnore) : pats')
    Pi Explicit m name src dst -> case pats of
      [] -> pure []
      (pat : pats) -> do
        pat' <- checkPattern st pat src
        pats' <- checkPatterns st loc (depth + 1) pats dst
        pure (pat':pats')
    ty -> if L.null pats
      then pure []
      else C.lift (Left (
        "\nthe function type\n" ++
        showTerm (signature st) [] ty ++
        "\ntakes " ++ show depth ++ " arguments, but this clause has " ++
        show (depth + length pats)))

checkPattern :: ElabState -> Pattern -> Term -> PC LPattern
checkPattern st pat ty = do
  label <- newLabel
  let ty' = whnf (signature st) [] ty
  case ty' of
    App (Ind block defno _) iargs -> case pat of
      PAbsurd loc -> pure (label, CAbsurd loc)
      PIgnore _ -> pure (label, CIgnore)
      PApp loc nloc name args -> let
        ind = sigInd (signature st) ! block !! defno
        ctors = introRules ind
        names = fmap fst ctors
        tag = elemIndex name names
        pno = paramno ind
        params = L.take pno iargs
        in case L.lookup name ctors of
          Nothing ->
            if L.null args
            then pure (label, CVar nloc name)
            else C.lift $ Left (show loc ++ 
            "\n`" ++ name ++ "` is not a constructor of type " ++ indName ind)
          Just ty -> let
            ctorArity (Pi Implicit _ _ _ dst) = ctorArity dst
            ctorArity (Pi Explicit _ _ _ dst) = ctorArity dst + 1
            ctorArity _  = 0
            
            ty' = instantiateCtor params ty
            arity = ctorArity ty
            
            argc = length args
            in if arity == argc
              then do
                args' <- checkPatterns st loc 0 args ty'
                pure (label, CCon loc (fromJust tag) args')
              else C.lift $ Left (show loc ++
                "\nconstructor " ++ name ++
                " of type " ++ indName ind ++ "\n" ++
                "expects " ++ show arity ++ " arguments, but got " ++ show argc)
    _ -> case pat of
      PAbsurd loc -> C.lift $ Left (show loc ++
        "\nabsurd pattern has type\n" ++
        showTerm (signature st) [] ty' ++
        "\nbut must be of some datatype\n")
      PIgnore _ -> pure (label, CIgnore)
      PApp loc nloc name [] -> pure (label, CVar nloc name)
      PApp loc nloc name args -> C.lift $ Left (show loc ++
        "\napplication pattern has type\n" ++
        showTerm (signature st) [] ty' ++
        "\nbut must be of some datatype\n")


