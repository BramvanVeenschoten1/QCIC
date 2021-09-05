module Prettyprint where

--import Lexer(Loc)
--import Parser
import Core
import Utils

import Data.Maybe
import Data.Map
import Data.List
import Prelude

{-
showMap :: (Show k, Show v) => Map k v -> String
showMap m = intercalate "\n" entries where
  entries = fmap showEntry (toList m)
  showEntry (dbl,val) = show dbl ++ " => " ++ show val

instance Show Term where
  show = showTerm []

showSubst :: Substitution -> String
showSubst subst = intercalate "\n" entries where
  entries = fmap showEntry (toList subst)
  showEntry (dbl,val) = show dbl ++ " <- " ++ showTerm [] val

showCaseTree :: Tree -> String
showCaseTree (Lam body) = '\\' : showCaseTree body
showCaseTree (Body t) = showTerm [] t
showCaseTree (Case n alts) = "case " ++ show n ++ "{" ++ intercalate "; " (zipWith showAlt [0..] alts) ++ "}" where
  showAlt n alt = show n ++ " => " ++ showCaseTree alt
showCaseTree (Refuted n) = '{' : show n ++ "}"
-}

embrace :: String -> String
embrace x = '(' : x ++ ")"

bracePi :: Term -> String -> String
bracePi (Pi {}) = embrace
bracePi _ = id

braceApp :: Term -> String -> String
braceApp (App _ []) = id
braceApp (App {}) = embrace
braceApp _ = id

showTerm :: Signature -> Context -> Term -> String
showTerm sig ctx x = case x of
  Type -> "Type"
  Kind -> "Kind"
  App f xs -> showHead f ++ concatMap (showArg ctx) xs
  Lam p m name ta b -> "\\" ++ name ++ ", " ++ showTerm sig (Hyp name ta Nothing : ctx) b
  Pi p m name ta tb ->
    let 
      ta' = bracePi ta (showTerm sig ctx ta)
      tb' = showTerm sig (Hyp name ta Nothing : ctx) tb
      mult = case m of
        Zero -> "0 "
        One  -> "1 "
        Many -> ""
      arrow = case m of
        Zero -> " => "
        One  -> " -o "
        Many -> " -> "
      pl = case p of
        Implicit -> ("{"++) . (++"}")
        Explicit -> id
    in
     if occurs 0 tb
     then "Pi " ++ pl (mult ++ name ++ " : " ++ ta') ++ ", " ++ tb'
     else ta' ++ arrow ++ tb'

  where
    
    showHead :: Head -> String
    showHead hd = case hd of 
      Var n -> hypName (fromJust (nth n ctx))
      Met n -> "?M" ++ show n
      Def blockno defno _ _ -> defName (sigDef sig ! blockno !! defno) 
      Ind blockno defno _ -> indName (sigInd sig ! blockno !! defno)
      Con blockno defno ctorno _ -> fst (introRules (sigInd sig ! blockno !! defno) !! ctorno)
    
    showArg ctx t = " " ++ braceApp t (showTerm sig ctx t)

showContext :: Signature -> Context -> String
showContext _ [] = ""
showContext sig (Hyp name ty val : ctx) =
  showContext sig ctx ++ "\n" ++ name ++ " : " ++ showTerm sig ctx ty

showQName :: [String] -> String
showQName = intercalate "."