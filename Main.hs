import Parser
import Modules

import Data.Functor
import Data.Map
import System.Environment
import System.IO
import Data.ByteString.Builder
import Control.Monad

{- here we do IO
get modules and verify, print signatures
-}

{- TODO
 - apply notes of equations
 - apply notes of typecheck
 - restrict large eliminations
 - restrict unification of types
 
 - decide on either:
   - implicit arguments may be relevant
   - implicit arguments are 0 regardless of annotation
 
 - improve prettyprinting, like in qtt2
 - implement type-driven disambiguation
 - parameter blocks
 - implement local pattern matching definitions / case blocks
 - implement records
 - implement type classes
 - commands
   partial, expect error, inlining and specialization, require erasedness, axioms,
   prettyprint flags? reflexive function optimization
 - infix syntax
 - destructuring let
 - local recursive definitions
 - have separate non-splitting definitions?
 - erasure to F-omega
 - have functions be implemented by primitives in compiled programs
   - numbers
   - switch
   - arrays
   - io
   - state
   - verified state?
   - words
 - enable kernel extension with rewrite rules for efficient primitives in typechecking
 - reflection
   - decision procedures
   - expose elabmonad
   - #derive commands
-}

main :: IO ()
main = getArgs >>= openFiles >>= checkFiles where

  openFiles :: [String] -> IO [(String,String)]
  openFiles = mapM (\name -> do
    file <- readFile name
    pure (name,file))

  checkFiles :: [(String,String)] -> IO ()
  checkFiles files =
    putStrLn $
    either id id $
    mapM (uncurry parse) files >>= checkModules
