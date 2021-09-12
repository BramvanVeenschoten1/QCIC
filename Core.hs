module Core where

import Data.Map

{-
  introduce temporary names for fixpoints currently in the
  elaborator? Or just use meta's?
  useful for:
  - having names that are typed but non-reducible
  - termination checks
  - positivity checks
  - lifting local definitions
  - lifting case expressions
  
  distinguish non-recursive definitions?
  
  are inductive blocks necessary for positivity checks?
  are fixpoint blocks necessary for termination checks?
  => both have a notion of uniform parameters
  => yes
  
-}

data Plicity = Implicit | Explicit

data Mult = Zero | One | Many deriving Eq

plus :: Mult -> Mult -> Mult
plus Zero x = x
plus x Zero = x
plus _ _ = Many

times :: Mult -> Mult -> Mult
times Zero _ = Zero
times _ Zero = Zero
times One x = x
times x One = x
times _ _ = Many

data Head
  = Var  Int
  | Met  Int           
  | Def  Int Int Int Int -- obj_id, defno, uniparamno, height
  | Ind  Int Int Int     -- obj_id, defno, uniparamno
  | Con  Int Int Int Int -- obj_id, defno, ctorno, paramno
  deriving (Eq, Ord)

data Term
  = Type
  | Kind
  | App Head [Term]
  | Let String Term Term Term
  | Lam Plicity Mult String Term Term
  | Pi  Plicity Mult String Term Term

-- the temptation arises to implement the env filter in regular term applications,
-- and have the clauses as closed terms
data Tree
  = Body  Int [Int]
  | Intro String Tree
  | Case  Int [([String],Tree)]

data Inductive = Inductive {
  indName    :: String,
  indSort    :: Term,
  paramno    :: Int, -- non-uniform parameters
  introRules :: [(String,Term)]} -- [(name, ty)]

data Definition = Definition {
  defName    :: String,
  defType    :: Term,
  defHeight  :: Int,
  defClauses :: [Term],
  defTree    :: Tree}

data Signature = Signature {
  sigInd :: Map Int [Inductive],
  sigDef :: Map Int [Definition]}

data Hyp = Hyp {
  hypName  :: String,
  hypType  :: Term,
  hypValue :: Maybe Term}

type Context = [Hyp]

--type Substitution = Map Int Term 
