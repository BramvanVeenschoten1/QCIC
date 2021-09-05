module Modules where

import Control.Monad
import Control.Monad.State.Lazy as C
import Core
import Data.Either
import Data.Function
import Data.List as L
import Data.Map as M
import Data.Maybe
import Debug.Trace

import Elaborator
import Declaration
import Lexer (Loc)
import Parser
import Prettyprint
import Utils

import Control.Monad.RWS

modName (n, _, _) = n

sortDependencies :: [Module] -> Either String [Module]
sortDependencies mods = fmap reverse (topological [] [] mods)
  where
    findModule name =
      maybe
        (Left ("unknown module: " ++ name))
        pure
        (find ((== name) . modName) mods)

    topological exploring explored [] = pure explored
    topological exploring explored (mod@(name, children, _) : mods)
      | name `elem` exploring = Left ("circular imports: " ++ unwords exploring)
      | name `elem` fmap modName explored = topological exploring explored mods
      | otherwise = do
        children' <- mapM findModule children
        explored' <- topological (name : exploring) explored children'
        topological exploring (mod : explored') mods

checkModules :: [Module] -> Either String String
checkModules mods = do
  runStateT
    (lift (sortDependencies mods) >>= mapM_ checkModule)
    (mempty, ElabState 0 mempty mempty mempty emptyObjects)

  pure ("\nok, defined modules:\n" ++ unlines (fmap modName mods))

checkModule :: Module -> StateT (Map Name NameSpace, ElabState) (Either String) ()
checkModule (name, imports, decls) = do
  (names, st) <- get

  let 
      st' = st {
        moduleName = name,
        importedNames = L.foldl (\acc imp -> mergeNameSpace acc (names ! imp)) mempty imports,
        internalNames = mempty}

  blocks <- C.lift (groupDecls decls)
  st'' <- C.lift (checkBlocks blocks st')

  put (M.insert name (internalNames st'') names, st'')
