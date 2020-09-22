{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Facet.Parser
( decl
, type'
, expr
) where

import           Control.Applicative (Alternative(..), liftA2, (<**>))
import           Data.Functor.Identity
import qualified Facet.Syntax.Untyped.Lifted as S
import           Prelude hiding (lines, null, span)
import           Text.Parser.Char
import           Text.Parser.Combinators
import           Text.Parser.Token hiding (ident)

-- case
-- : (x : a) -> (f : a -> b) -> b
-- { f x }

-- TODO:
-- list literals
-- numeric literals
-- forcing nullary computations
-- holes

-- FIXME: this runs into problems when binders capture a variable sharing a prefix w/ other used vars.
decl :: forall p expr ty decl mod . (S.Module expr ty decl mod, S.Err ty, S.Err expr, Monad p, TokenParsing p) => p mod
decl = (S..:) <$> ident <* colon <*> (runIdentity <$> sig (fmap pure global) (fmap pure tglobal))
  where
  sig :: S.Permutable env' => p (env' expr) -> p (env' ty) -> p (env' decl)
  sig var tvar = liftA2 (S..=) <$> type_ tvar <*> expr_ var <|> bind var tvar <|> forAll sig var tvar

  bind :: S.Permutable env' => p (env' expr) -> p (env' ty) -> p (env' decl)
  bind var tvar = lparen *> (ident >>= \ i -> spaces *> colon *> (type_ tvar S.>-> \ t -> rparen *> arrow *> sig (S.weaken var <|> t <$ variable i) (S.weaken tvar)))


forAll
  :: forall env ty res p x
  .  (S.Permutable env, S.ForAll ty res, S.Type ty, S.Err ty, Monad p, TokenParsing p)
  => (forall env' . S.Permutable env' => p (env' x) -> p (env' ty) -> p (env' res))
  -> p (env x)
  -> p (env ty)
  -> p (env res)
forAll k x tvar = lbrace *> names []
  where
  names is = tident >>= \ i ->
        comma *> names (fmap pure (variable i):is)
    <|> colon *> (type_ tvar <* rbrace <* arrow >>= \ t -> types (pure t) x tvar (reverse (fmap pure (variable i):is)))
  types :: S.Permutable env' => p (env' ty) -> p (env' x) -> p (env' ty) -> [p (env' S.Name)] -> p (env' res)
  types ty x tvar = \case
    []   -> k x tvar
    i:is -> ty S.>=> \ t -> types (S.weaken ty) (S.weaken x) (S.weaken tvar <|> t <$ i) (map S.weaken is)


type' :: (S.Type ty, S.Err ty, Monad p, TokenParsing p) => p ty
type' = runIdentity <$> type_ (fmap pure tglobal)

type_ :: (S.Permutable env, S.Type ty, S.Err ty, Monad p, TokenParsing p) => p (env ty) -> p (env ty)
type_ tvar = fn tvar <|> forAll (const type_) (pure <$> char '_') tvar <?> "type"

fn :: (S.Permutable env, S.Type ty, S.Err ty, Monad p, TokenParsing p) => p (env ty) -> p (env ty)
fn tvar = app tatom tvar <**> (flip (liftA2 (S.-->)) <$ arrow <*> fn tvar <|> pure id)

tatom :: (S.Permutable env, S.Type ty, S.Err ty, Monad p, TokenParsing p) => p (env ty) -> p (env ty)
tatom tvar
  =   parens (prd <$> sepBy (type_ tvar) comma)
  <|> tvar
  <|> pure S._Type <$ string "Type"
  where
  prd [] = pure S._Unit
  prd ts = foldl1 (liftA2 (S..*)) ts

tglobal :: (S.Type ty, TokenParsing p) => p ty
tglobal = S.tglobal <$> tident <?> "variable"


expr :: (S.Expr expr, S.Err expr, Monad p, TokenParsing p) => p expr
expr = runIdentity <$> expr_ (pure <$> global)

global :: (S.Expr expr, TokenParsing p) => p expr
global = S.global <$> ident <?> "variable"

expr_ :: forall p env expr . (S.Permutable env, S.Expr expr, S.Err expr, Monad p, TokenParsing p) => p (env expr) -> p (env expr)
expr_ = app atom

-- FIXME: patterns
-- FIXME: nullary computations
-- FIXME: the variable is parsed even when it’s a prefix of a longer identifier
lam :: forall p env expr . (S.Permutable env, S.Expr expr, S.Err expr, Monad p, TokenParsing p) => p (env expr) -> p (env expr)
lam var = braces $ clause var
  where
  clause :: S.Permutable env' => p (env' expr) -> p (env' expr)
  clause var = S.lam0 (\ v -> ident >>= \ i -> let var' = S.weaken var <|> v <$ variable i in clause var' <|> arrow *> expr_ var') <?> "clause"

atom :: (S.Permutable env, S.Expr expr, S.Err expr, Monad p, TokenParsing p) => p (env expr) -> p (env expr)
atom var
  =   lam var
  <|> parens (prd <$> sepBy (expr_ var) comma)
  <|> var
  where
  prd [] = pure S.unit
  prd ts = foldl1 (liftA2 (S.**)) ts

app :: (S.Permutable env, S.App expr, TokenParsing p) => (p (env expr) -> p (env expr)) -> (p (env expr) -> p (env expr))
app atom tvar = foldl (liftA2 (S.$$)) <$> atom tvar <*> many (atom tvar)


identS, ident, tidentS, tident :: TokenParsing p => p S.Name
identS = (:) <$> lower <*> many letter
ident = token identS
tidentS = (:) <$> upper <*> many letter
tident = token tidentS

arrow :: TokenParsing p => p String
arrow = token (string "->")

lparen, rparen :: TokenParsing p => p Char
lparen = symbolic '('
rparen = symbolic ')'

lbrace, rbrace :: TokenParsing p => p Char
lbrace = symbolic '{'
rbrace = symbolic '}'

variable :: TokenParsing p => String -> p String
variable s = token (string s) <* notFollowedBy alphaNum
