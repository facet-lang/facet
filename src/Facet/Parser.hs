{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Parser
( decl
, type'
, expr
) where

import           Control.Applicative ((<**>))
import           Data.Functor.Identity
import           Facet.Functor.C
import           Facet.Parser.Combinators
import qualified Facet.Syntax.Untyped.Lifted as S
import           Prelude hiding (fail, lines, null, span)

type Name = String

-- case
-- : (x : a) -> (f : a -> b) -> b
-- { f x }

decl :: (S.Module expr ty decl mod, S.Err decl, S.Err ty, S.Err expr, Parsing p) => p mod
decl = (S..:) <$> ident <* colon <*> sig


sig :: (S.Decl expr ty decl, S.Err decl, S.Err ty, S.Err expr, Parsing p) => p decl
sig = runIdentity <$> getC (sig_ global tglobal)

sig_ :: forall p env expr ty decl . (Permutable env, Parsing p, S.Decl expr ty decl, S.Err decl, S.Err ty, S.Err expr) => (p :.: env) expr -> (p :.: env) ty -> (p :.: env) decl
sig_ var tvar = (S..=) <$> type_ tvar <*> expr_ var <|> bind var tvar <|> forAll (sig_ (weaken var)) tvar
  where
  bind :: forall env . Permutable env => (p :.: env) expr -> (p :.: env) ty -> (p :.: env) decl
  bind var tvar = lparen *> capture (const id) identS (\ i -> ws *> colon *> (type_ tvar S.>-> \ t -> rparen *> arrow *> sig_ (weaken var <|> liftCOuter t <* weaken (token i)) (weaken tvar)))

-- FIXME: bind multiple type variables of the same kind in a single set of braces
forAll :: (Permutable env, S.ForAll ty res, S.Type ty, S.Err ty, Parsing p) => (forall env' . Extends env env' => (p :.: env') ty -> (p :.: env') res) -> (p :.: env) ty -> (p :.: env) res
forAll k tvar = lbrace *> capture (const id) identS (\ i -> ws *> colon *> (type_ tvar S.>=> \ t -> rbrace *> arrow *> k (weaken tvar <|> liftCOuter t <* weaken (token i))))


type' :: (S.Type ty, S.Err ty, Parsing p) => p ty
type' = runIdentity <$> getC (type_ tglobal)

type_ :: (Permutable env, S.Type ty, S.Err ty, Parsing p) => (p :.: env) ty -> (p :.: env) ty
type_ tvar = fn tvar <|> forAll type_ tvar <|> fail S.err "type"

fn :: (Permutable env, S.Type ty, S.Err ty, Parsing p) => (p :.: env) ty -> (p :.: env) ty
fn tvar = app tatom tvar <**> opt (flip (S.-->) <$ arrow <*> fn tvar) id

tatom :: (Permutable env, S.Type ty, S.Err ty, Parsing p) => (p :.: env) ty -> (p :.: env) ty
tatom tvar
  =   parens (prd <$> sepBy (type_ tvar) comma)
  <|> tvar
  <|> S._Type <$ string "Type"
  where
  prd [] = S._Unit
  prd ts = foldl1 (S..*) ts

tglobal :: (S.Type ty, Parsing p) => p ty
tglobal = S.tglobal <$> tident <?> (S.tglobal "_", "variable")


expr :: (S.Expr expr, S.Err expr, Parsing p) => p expr
expr = runIdentity <$> getC (expr_ global)

global :: (S.Expr expr, Parsing p) => p expr
global = S.global <$> ident <?> (S.global "_", "variable")

expr_ :: forall p env expr . (Permutable env, S.Expr expr, S.Err expr, Parsing p) => (p :.: env) expr -> (p :.: env) expr
expr_ = app atom

-- FIXME: patterns
lam_ :: forall p env expr . (Permutable env, S.Expr expr, S.Err expr, Parsing p) => (p :.: env) expr -> (p :.: env) expr
lam_ var = braces $ clause_ var
  where
  clause_ :: Permutable env' => (p :.: env') expr -> (p :.: env') expr
  clause_ var = S.lam0 (\ v -> capture (const id) identS (\ i -> let var' = weaken var <|> liftCOuter v <* token i in ws *> (clause_ var' <|> arrow *> expr_ var'))) <?> (S.err, "clause")

atom :: (Permutable env, S.Expr expr, S.Err expr, Parsing p) => (p :.: env) expr -> (p :.: env) expr
atom var
  =   lam_ var
  <|> parens (prd <$> sepBy (expr_ var) comma)
  <|> var
  where
  prd [] = S.unit
  prd ts = foldl1 (S.**) ts

app :: (Permutable env, S.App expr, Parsing p) => ((p :.: env) expr -> (p :.: env) expr) -> ((p :.: env) expr -> (p :.: env) expr)
app atom tvar = foldl (S.$$) <$> atom tvar <*> many (atom tvar)


identS, ident, tidentS, tident :: Parsing p => p Name
identS = (:) <$> lower <*> many letter
ident = token identS
tidentS = (:) <$> upper <*> many letter
tident = token tidentS

arrow :: Parsing p => p String
arrow = token (string "->")
