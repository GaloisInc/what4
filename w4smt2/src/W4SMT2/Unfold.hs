{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}

module W4SMT2.Unfold
  ( unfoldDefineFuns
  ) where

import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (mapMaybe)
import Data.Text (Text)
import What4.Protocol.SExp qualified as SExp
import W4SMT2.SExpPat (sexp)

-- | Function definition containing name, parameters, return type, body, and recursion flag
data FnDef = FnDef
  { fdName :: Text
  , fdParams :: [(Text, SExp.SExp)]  -- [(param_name, param_type)]
  , fdReturnType :: SExp.SExp
  , fdBody :: SExp.SExp
  , fdIsRecursive :: Bool
  } deriving (Show)

-- | Main entry point: unfold all define-fun applications
unfoldDefineFuns :: (?logStderr :: Text -> IO ()) => [SExp.SExp] -> IO [SExp.SExp]
unfoldDefineFuns sexps = do
  let (defs, rest) = collectDefinitions sexps

  -- Warn about recursive functions
  mapM_ warnRecursive (Map.filter fdIsRecursive defs)

  -- Keep recursive define-funs, unfold non-recursive ones
  let recursiveDefs = Map.filter fdIsRecursive defs
  let nonRecursiveDefs = Map.filter (not . fdIsRecursive) defs

  -- Reconstruct define-fun s-expressions for recursive functions
  let recursiveSExps = map reconstructDefineFun (Map.elems recursiveDefs)

  -- Unfold the rest using only non-recursive definitions
  let unfolded = unfoldSExps nonRecursiveDefs rest

  return $ recursiveSExps ++ unfolded
  where
    warnRecursive :: FnDef -> IO ()
    warnRecursive fnDef =
      ?logStderr $ "Warning: Skipping recursive function '" <> fdName fnDef <> "' - cannot unfold"

    reconstructDefineFun :: FnDef -> SExp.SExp
    reconstructDefineFun fnDef =
      let paramList = SExp.SApp [SExp.SApp [SExp.SAtom pname, ptype]
                                | (pname, ptype) <- fdParams fnDef]
      in SExp.SApp [SExp.SAtom "define-fun",
                    SExp.SAtom (fdName fnDef),
                    paramList,
                    fdReturnType fnDef,
                    fdBody fnDef]

-- | Collect all define-fun definitions and return remaining s-expressions
collectDefinitions :: [SExp.SExp] -> (Map Text FnDef, [SExp.SExp])
collectDefinitions = foldr go (Map.empty, [])
  where
    go sexpr (defs, rest) = case sexpr of
      [sexp|(define-fun #nameSexp #paramsSexp #retTypeSexp #bodySexp)|]
        | SExp.SAtom name <- nameSexp ->
            let params = parseParams paramsSexp
                isRec = isRecursive name bodySexp
                fnDef = FnDef name params retTypeSexp bodySexp isRec
            in (Map.insert name fnDef defs, rest)
      _ -> (defs, sexpr : rest)

-- | Parse parameter list: ((p1 T1) (p2 T2) ...)
parseParams :: SExp.SExp -> [(Text, SExp.SExp)]
parseParams (SExp.SApp params) = mapMaybe parseParam params
  where
    parseParam [sexp|(#pname #ptype)|]
      | SExp.SAtom name <- pname = Just (name, ptype)
    parseParam _ = Nothing
parseParams _ = []

-- | Check if a function is recursive (appears in its own body)
isRecursive :: Text -> SExp.SExp -> Bool
isRecursive fnName = go
  where
    go (SExp.SAtom name) = name == fnName
    go (SExp.SApp []) = False
    go (SExp.SApp (hd:args)) = go hd || any go args  -- Check head and all arguments
    go _ = False

-- | Unfold all s-expressions using the given function definitions
unfoldSExps :: Map Text FnDef -> [SExp.SExp] -> [SExp.SExp]
unfoldSExps defs = map (unfoldSExp defs)

-- | Recursively unfold a single s-expression
unfoldSExp :: Map Text FnDef -> SExp.SExp -> SExp.SExp
unfoldSExp defs = go
  where
    -- Handle zero-parameter functions (bare atoms)
    go (SExp.SAtom fnName) =
      case Map.lookup fnName defs of
        Just fnDef
          | not (fdIsRecursive fnDef)
          , null (fdParams fnDef) ->
              -- Zero-param function: unfold directly to body
              go (fdBody fnDef)
        _ -> SExp.SAtom fnName
    -- Handle function applications
    go (SExp.SApp (SExp.SAtom fnName : args)) =
      case Map.lookup fnName defs of
        Just fnDef
          | not (fdIsRecursive fnDef)
          , length args == length (fdParams fnDef) ->
              -- Unfold: create let-binding and recursively unfold body
              go (buildLetBinding fnDef (map go args))
        _ ->
              -- Not a define-fun or recursive: just recurse on children
              SExp.SApp (SExp.SAtom fnName : map go args)
    go (SExp.SApp xs) = SExp.SApp (map go xs)
    go other = other

-- | Build a let-binding for function application
buildLetBinding :: FnDef -> [SExp.SExp] -> SExp.SExp
buildLetBinding fnDef args
  | null (fdParams fnDef) = fdBody fnDef  -- Zero-param: direct substitution
  | otherwise =
      let bindings = SExp.SApp [SExp.SApp [SExp.SAtom pname, arg]
                               | ((pname, _), arg) <- zip (fdParams fnDef) args]
      in SExp.SApp [SExp.SAtom "let", bindings, fdBody fnDef]
