module Utils where

import Core

import Data.List as L
import Data.Map as M
import Data.Maybe
import Data.Map hiding (foldr)

{- based on the matita kernel -}
{- here we have utilities for iterating over core terms -}

type Substitution = Map Int Term
type MetaEnv = Map Int Term

nth :: Int -> [a] -> Maybe a
nth 0 (x : _) = Just x
nth n (_ : xs) = nth (n-1) xs
nth _ _ = Nothing

applyFilter :: [Int] -> [a] -> [a]
applyFilter f xs = fmap (\n -> fromMaybe (error "bad filter") (nth n xs)) f

fold :: (Hyp -> k -> k) -> k -> (k -> Term -> a -> a) -> Term -> a -> a
fold push ctx f t acc = case t of
  App fun args -> L.foldr (f ctx) acc args
  Pi  p m name src dst -> f ctx src (f (push (Hyp name src Nothing) ctx) dst acc)
  Lam p m name src dst -> f ctx src (f (push (Hyp name src Nothing) ctx) dst acc)
  Let name ta a b -> f ctx ta (f ctx a (f (push (Hyp name ta (Just a)) ctx) b acc))
  _ -> acc

map :: (Hyp -> k -> k) -> k -> (k -> Term -> Term) -> Term -> Term
map push ctx f t = case t of
  App fun args -> App fun (fmap (f ctx) args)
  Pi p m name src dst -> Pi p m name (f ctx src) (f (push (Hyp name src Nothing) ctx) dst)
  Lam p m name src dst -> Lam p m name (f ctx src) (f (push (Hyp name src Nothing) ctx) dst)
  Let name ta a b -> Let name (f ctx ta) (f ctx a) (f (push (Hyp name ta (Just a)) ctx) b)
  t -> t

-- inclusive range of dbis
doesNotOccur :: Context -> Int -> Int -> Term -> Bool
doesNotOccur ctx n nn t = not (occurs ctx n nn t) -- f 0 t True
  where
    f _ _ False = False
    f k (App (Var m) args) acc
      | m >= n + k && m <= nn + k = L.foldr (f k) acc args
      | m < k && m > nn + k = True
      | otherwise = True
    f k t _ = Utils.fold (const (+1)) k f t True
  
occurs :: Context -> Int -> Int -> Term -> Bool
occurs ctx min max t = f 0 t False where
  f k (App (Var n) args) acc =
    n >= min + k && n <= max + k || L.foldr (f k) acc args
  f k t acc = Utils.fold (const (+1)) k f t acc

countDomains :: Term -> Int
countDomains (Pi p m name src dst) = 1 + countDomains dst
countDomains _ = 0

occursMet :: Int -> Term -> Bool
occursMet n t = f () t False where
  f () (App (Met n') args) acc = n == n' || L.foldr (f ()) acc args
  f () t acc = Utils.fold (const id) () f t acc

metaVars :: Term -> [Int]
metaVars t = f () t [] where
  f () (App head args) acc = g head (L.foldr (f ()) acc args)
  f () t acc = Utils.fold (const id) () f t acc
  
  g (Met n) acc = L.insert n acc
  g _ acc = acc

{- get the largest number of parameters that are uniformly applied to all recursive occurences -}
{- may be useable for fixpoints as well?
   => must be adapted for nested calls, eg:
      f x (f y)

getUniparamno :: Term -> Int -> Int
getUniparamno = f 0 where
  eatArgs n (App (DBL m) [] : args) acc
    | n == m = eatArgs (n - 1) args (acc + 1)
  eatArgs _ _ acc = acc

  f k (App (DBL m) args) acc
    | m >= k = min acc (eatArgs (k - 1) args 0)
  f k t a = Utils.fold (const (+1)) k f t a
  -}
