module Substitution where

import Utils
import Core
import Data.List
import Data.Map as M
import Data.Maybe

{- here be substitution and lifting -}

liftFrom :: Int -> Int -> Term -> Term
liftFrom k n = f k where
  f k (App (Var m) xs)
    | m >= k = App (Var (m + n)) (fmap (liftFrom k n) xs)
  f k (App head xs) = App head (fmap (liftFrom k n) xs)
  f k (Pi p m name ta tb) = Pi p m name (liftFrom k n ta) (liftFrom (k + 1) n tb)
  f k t = t

lift :: Int -> Term -> Term
lift = liftFrom 0

psubst :: [Term] -> Term -> Term
psubst args = f 0 where
  nargs = length args
  
  h k (t @ (Var n)) args'
    | n >= k + nargs = App (Var (n - nargs)) args'
    | n < k          = App t args'
    | otherwise      = case lift k (fromMaybe (error "Var in subst out of range") (nth (n - k) args)) of
      App f args'' -> App f (args'' ++ args')
      pi -> pi
  h _ t args' = App t args'
  
  f k (App fun args) = h k fun (fmap (f k) args)
  f k (Pi p m name src dst) = Pi p m name (f k src) (f (k + 1) dst)
  f k x = x

subst :: Term -> Term -> Term
subst = psubst . (:[])

instantiateCtor :: [Term] -> Term -> Term
instantiateCtor params t = psubst (reverse params) (dropDomains (length params) t) where
  dropDomains :: Int -> Term -> Term
  dropDomains 0 tb = tb
  dropDomains n (Pi _ _ _ _ tb) = dropDomains (n - 1) tb

applySubst :: Map Int Term -> Term -> Term
applySubst sub t = f 0 t where
  f k (App head args) = mkApp (g k head) (fmap (f k) args)
  f k t = Utils.map (const (+1)) k f t
  
  g k (Met n) = case M.lookup n sub of
    Just x -> f k (lift k x)
    Nothing -> App (Met n) []
  g k t = App t []

{- substitute recursive occurrences of inductives or fixpoints for positiviy analysis-}
substWithDummy :: Int -> Term -> Term
substWithDummy block_no = f () where
  f _ (App (Ind obj_id _ upno) args)
    |  obj_id == block_no =
      App (Met 0) (Data.List.drop upno args)
  f _ t = Utils.map (const id) () f t

