module Parser where

import Lexer hiding (keywords, puncts)
import Core

import Control.Applicative
import Data.List ()
import Data.Function ()
import Data.Array.Unboxed ( listArray )
import Data.Maybe ( isJust )
import Control.Monad.RWS
import Debug.Trace

type Name = String
type QName = [Name]
type Param = (Plicity, Mult, String, Expr)
type Ctor = (String, Expr)
type Clause = (Loc,[Pattern],Expr)

data Pattern
  = PAbsurd Loc
  | PIgnore Loc
  | PApp Loc Loc String [Pattern]

type Module = (String,[String],[Decl])

data Decl 
  = DataDecl Loc String [Param] Expr
  | DataDef  Loc String [Ctor]
  | FunDecl  Loc String Expr
  | Clause   Loc String [Pattern] Expr

data EHead
  = EVar Loc String
  | EName Loc [String]

data Expr 
  = EType  Loc
  | EApply Loc EHead [(Plicity,Expr)]
  | EPi    Loc Plicity Mult String Expr Expr
  | ELet   Loc Loc String (Maybe Expr) Expr Expr
  | ELam   Loc Loc String Expr 

headLoc :: EHead -> Loc
headLoc (EName s _) = s
headLoc (EVar s _) = s

exprLoc :: Expr -> Loc
exprLoc (EType s) = s
exprLoc (ELam s _ _ _) = s
exprLoc (EApply s _ _) = s
exprLoc (EPi s _ _ _ _ _) = s
--exprLoc (EHole s) = s

puncts :: [String]
puncts = ["->", "-o", "=>", "=" , "()", "(" , ")" , "{", "}", "[", "]", "\\" , ".", ":", ","]

keywords :: [String]
keywords = [
  "_",
  "module",
  "import",
  "mutual",
  "data",
  "where",
  "case",
  "of",
  "let",
  "in",
  "Pi", 
  "Type"]

parseQName :: Cursor -> String -> Parser Expr
parseQName begin x = do
  t <- peekToken
  case t of
    Pct "." -> do
      xs  <- tail
      loc <- endLoc begin
      pure (mkApp (EName loc (x:xs)))
    _ -> do
      loc <- endLoc begin
      pure (mkApp (EVar loc x))
    where
      mkApp hd = EApply (headLoc hd) hd []
      tail = do
        token
        x <- expectSymbol "symbol after '.' in qualified name"
        t <- peekToken
        case t of
          Pct "." -> do
            xs <- tail
            pure (x:xs)
          _ -> pure [x]

annot :: Parser Expr
annot = do
  expect ":" "':' after names in parameters"
  parseExpr

parseMult :: Parser Mult
parseMult = do
  t <- peek token 
  case t of
    Number 0 -> fmap (const Zero) token
    Number 1 -> fmap (const One) token
    _ -> pure Many

annotParam :: Plicity-> Parser [Param]
annotParam p = do
  m  <- parseMult
  bs <- some ((expect "_" "" >> pure "") <|>
          expectSymbol "name in parameter list")
  ty <- annot
  pure (fmap (\name -> (p,m,name,ty)) bs)

param :: Parser [Param]
param = do
  t <- peekToken
  case t of
    Pct "(" -> token *> annotParam Explicit <* f ")"
    Pct "{" -> token *> annotParam Implicit <* f "}"
--    Pct "[" -> token *> annotParam Class <* f "]"
    Pct "_" -> annotParam Explicit
    _ -> annotParam Explicit
  where f close = expect close ("closing '" ++ close ++ "' after parameter")

params :: Parser [Param]
params = do
  t <- peekToken
  case t of
    Symbol _ -> someParams
    Pct "("  -> someParams
    Pct "{"  -> someParams
    Pct "["  -> someParams
    Pct "_"  -> someParams 
    _ -> pure []
  
someParams :: Parser [Param]
someParams = (++) <$> param <*> params

-- parse a lambda or dependent product,
-- having already consumed the 'fun' or 'Pi' token
parsePi :: Cursor -> Parser Expr
parsePi begin = do
  ps <- someParams
  expect "," "',' after parameters in binder"
  body <- parseExpr
  loc <- endLoc begin
  let f (p,m,v,ta) = EPi loc p m v ta
  pure (foldr f body ps)
  
parseLambda :: Cursor -> Parser Expr
parseLambda begin = do
  ps <- some (withLoc (expectSymbol "name in lambda binding"))
  expect "," "',' after parameters in binder"
  body <- parseExpr
  loc <- endLoc begin
  let f (nloc,v) = ELam loc nloc v
  pure (foldr f body ps)

parseLet :: Cursor -> Parser Expr
parseLet begin = do
  (nloc,name) <- withLoc (expectSymbol "name after 'let' keyword")
  let f ty = do
        expect "=" "'=' after name in let expression"
        bindee <- parseExpr
        expect "in" "'in' after binding in let expression"
        body <- parseExpr
        loc <- endLoc begin
        pure (ELet loc nloc name ty bindee body)
  t <- peekToken
  case t of
    Pct ":" -> token *> parseExpr >>= f . Just
    _ -> f Nothing

{-
parseCase :: Cursor -> Parser Expr
parseCase begin = do
  scrutinee <- parseExpr
  let f motive = do
        expect "of" "'of' after scrutinee in case expression"
        arms <- parseBlock parseArm
        loc <- endLoc begin
        --pure (ECase loc scrutinee motive arms)
        error "cannot parse case-expressions because not implemented"

      parseArm = do
        x <- expectSymbol "constructor name in case arm"
        (xs,rhs) <- parseSubs
        pure (x,xs,rhs)

      parseSubs = do
        (loc,t) <- withLoc token
        case t of
          Pct "->" -> (,) [] <$> parseExpr
          Symbol x -> do
            (xs,rhs) <- parseSubs
            pure (x:xs,rhs)
          _ -> expected loc "a symbol in case arm" (show loc)

  t <- peekToken
  case t of
    Pct "return" -> token *> parseExpr >>= f
    _ -> endLoc begin >>= f . EHole
-}
{-
parsePrim :: Cursor -> (Loc -> Int -> Expr) -> Parser Expr
parsePrim begin mk = do
  t <- peekToken
  case t of
    Number l -> do
      token
      loc <- endLoc begin
      pure (mk loc (l + 1))
    _ -> do
      loc <- endLoc begin
      pure (mk loc 1)
-}

parsePrimary :: Parser Expr
parsePrimary = do
  begin   <- beginLoc
  (loc,t) <- withLoc token
  case t of
    Pct "(" ->
      parseExpr <* expect ")" "closing ')' after parseExpression"
    Pct "\\" -> parseLambda begin
    Pct "Type" -> pure (EType loc)
    Pct "Pi" -> parsePi begin
    Pct "let" -> parseLet begin
--    Pct "case" -> parseCase begin
    Symbol x -> parseQName begin x
    x -> expected loc "some parseExpression" (show loc)

parseApp :: Cursor -> Parser Expr
parseApp begin = do
  head <- parsePrimary
  case head of
    EApply loc hd [] -> do
      let
        parseArgs :: Parser [(Plicity,Expr)]
        parseArgs = do
          blockEnds <- isBlockEnd
          if blockEnds
          then pure []
          else do
            t <- peekToken
            case t of
              Symbol _    -> expArg
              Pct "_"     -> expArg
              Pct "Type"  -> expArg
              Pct "\\"    -> expArg
              Pct "Pi"    -> expArg
              Pct "let"   -> expArg
              Pct "case"  -> expArg
              Pct "("     -> expArg
              Pct "{"     -> impArg
              _           -> pure []
        
        expArg = do
          arg <- parsePrimary
          args <- parseArgs
          pure ((Explicit,arg):args)
        
        impArg = do
          token
          arg <- parseExpr
          expect "}" "closing '}' after implicit argument"
          args <- parseArgs
          pure ((Implicit,arg):args)
      args <- parseArgs
      loc <- endLoc begin
      pure (EApply loc hd args)
    e -> pure e

parseArrow :: Parser Expr
parseArrow = do
  begin <- beginLoc
  lhs   <- parseApp begin
  t     <- peekToken
  case t of
    Pct "->" -> f Many begin lhs
    Pct "-o" -> f One  begin lhs
    Pct "=>" -> f Zero begin lhs
    _ -> pure lhs
    where
      f m begin lhs = do
        token
        rhs <- parseArrow
        loc <- endLoc begin
        pure (EPi loc Explicit m "" lhs rhs)

parseExpr :: Parser Expr
parseExpr = parseArrow

parseAppPattern :: Parser Pattern
parseAppPattern = do
  begin       <- beginLoc
  (nloc,name) <- withLoc $ expectSymbol "constructor name in application pattern"
  args        <- parsePatterns
  loc         <- endLoc begin
  pure (PApp loc nloc name args)
 
parseClosedPattern :: Parser Pattern
parseClosedPattern = do
  (loc,t) <- withLoc token
  case t of
    Pct "(" -> do
      app <- parseAppPattern
      expect ")" "closing ')' after pattern"
      pure app
    Pct "_" -> pure (PIgnore loc)
    Symbol x -> do
      pure (PApp loc loc x [])

parsePatterns :: Parser [Pattern]
parsePatterns = do
  t <- peekToken
  case t of
    Symbol _ -> pat
    Pct "("  -> pat
    Pct "_"  -> pat
    _ -> pure []
  where
    pat = (:) <$> parseClosedPattern <*> parsePatterns

-- parse a function clause, having already consumed the name
parseClause :: Loc -> String -> Parser Decl
parseClause loc name = do
  pats <- parsePatterns
  (loc,t) <- withLoc token
  case t of
    Pct "=" -> parseExpr >>= f pats
    Pct "()" -> f (pats ++ [PAbsurd loc]) (EType loc)
    _ -> expected loc "'=' or '()' after patterns in clause" (show loc)
  where
    f pats body = pure (Clause loc name pats body)

parseConstructor :: Parser Ctor
parseConstructor = do
  name <- expectSymbol "name in constructor definition"
  expect ":" "':' after name in constructor definition"
  ty <- parseExpr
  pure (name,ty)

-- parse a data declaration/definition,
-- having already consumed the 'data' keyword
parseData :: Parser [Decl]
parseData = do
  (loc,name) <- withLoc (expectSymbol "name after 'data' in data declaration")
  ps <- params
  arity <- do
    t <- peekToken
    case t of
      Pct ":" -> token >> fmap Just parseExpr
      _ -> pure Nothing
  ctors <- do
    t <- peekToken
    case t of
      Pct "where" -> token >> fmap Just (parseBlock parseConstructor)
      _ -> pure Nothing

  case (arity,ctors) of
    (Nothing, Nothing) -> errAt loc "data declaration must have a declaration and constructor block"
    (Nothing, Just ctors) -> pure [DataDef loc name ctors]
    (Just arity, Nothing) -> pure [DataDecl loc name ps arity]
    (Just arity, Just ctors) -> pure
      [DataDecl loc name ps arity,
      DataDef loc name ctors]

-- parse a function clause/declaration, having already consumed the symbol
parseFunction :: Loc -> String -> Parser Decl
parseFunction loc name = do
  t <- peekToken
  case t of
    Pct ":" -> token *> (FunDecl loc name <$> parseExpr)
    _ -> parseClause loc name 

-- parse declarations
parseDecl :: Parser [Decl]
parseDecl = do
  (loc,t) <- withLoc token
  case t of
    Pct ""     -> pure []
    Pct "data" -> parseData
    Symbol x   -> (:[]) <$> parseFunction loc x
    x -> err (show loc ++ "expected some declaration")

-- parse module import statements
parseImports :: Parser [String]
parseImports = do
  t <- peekToken
  case t of
    Pct "import" -> do
      token
      parseBlock (expectSymbol "name after 'import'")
    _ -> pure []

parseModule :: Parser Module
parseModule = do
  expect "module" "module name declaration"
  name <- expectSymbol "name after 'module'"
  imports <- parseImports
  decls <- concat <$> parseItems 0 parseDecl
  pure (name,imports,decls)

parse :: Filename -> String -> Either ParseError Module
parse name input = do
  fst <$> evalRWST
            parseModule
            (ParserEnv keywords puncts name (listArray (0, length input - 1) input) [0])
            (Cursor 0 0 0)
