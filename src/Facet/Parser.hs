{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
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

-- case
-- : (x : a) -> (f : a -> b) -> b
-- { f x }

-- TODO:
-- list literals
-- numeric literals
-- forcing nullary computations
-- holes

-- FIXME: this runs into problems when binders capture a variable sharing a prefix w/ other used vars.
decl :: forall p expr ty decl mod . (S.Module expr ty decl mod, S.Err ty, S.Err expr, Parsing p) => p mod
decl = (S..:) <$> ident <* colon <*> (runIdentity <$> getC (sig global tglobal))
  where
  sig :: Permutable env => (p :.: env) expr -> (p :.: env) ty -> (p :.: env) decl
  sig var tvar = (S..=) <$> type_ tvar <*> expr_ var <|> bind var tvar <|> forAll sig var tvar

  bind :: forall env . Permutable env => (p :.: env) expr -> (p :.: env) ty -> (p :.: env) decl
  bind var tvar = lparen *> capture (const id) identS (\ i -> ws *> colon *> (type_ tvar S.>-> \ t -> rparen *> arrow *> sig (weaken var <|> liftCOuter t <* weaken (token i)) (weaken tvar)))


forAll
  :: forall env ty res p x
  .  (Permutable env, S.ForAll ty res, S.Type ty, S.Err ty, Parsing p)
  => (forall env' . Permutable env' => (p :.: env') x -> (p :.: env') ty -> (p :.: env') res)
  -> (p :.: env) x
  -> (p :.: env) ty
  -> (p :.: env) res
forAll k x tvar = lbrace *> names []
  where
  names is = capture (const id) tidentS $ \ i -> ws *>
    (   comma *> names (i:is)
    <|> colon *> capture0 (const id) (type_ tvar <* rbrace <* arrow) (\ t -> types t x tvar (reverse (i:is))))
  types :: Permutable env' => (p :.: env') ty -> (p :.: env') x -> (p :.: env') ty -> [(p :.: env') S.Name] -> (p :.: env') res
  types ty x tvar = \case
    []   -> k x tvar
    i:is -> ty S.>=> \ t -> types (weaken ty) (weaken x) (weaken tvar <|> liftCOuter t <* weaken (token i)) (map weaken is)


type' :: (S.Type ty, S.Err ty, Parsing p) => p ty
type' = runIdentity <$> getC (type_ tglobal)

type_ :: (Permutable env, S.Type ty, S.Err ty, Parsing p) => (p :.: env) ty -> (p :.: env) ty
type_ tvar = fn tvar <|> forAll (const type_) (char '_') tvar <|> fail S.err "type"

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
-- FIXME: nullary computations
lam :: forall p env expr . (Permutable env, S.Expr expr, S.Err expr, Parsing p) => (p :.: env) expr -> (p :.: env) expr
lam var = braces $ clause var
  where
  clause :: Permutable env' => (p :.: env') expr -> (p :.: env') expr
  clause var = S.lam0 (\ v -> capture (const id) identS (\ i -> let var' = weaken var <|> liftCOuter v <* token i in ws *> (clause var' <|> arrow *> expr_ var'))) <?> (S.err, "clause")

atom :: (Permutable env, S.Expr expr, S.Err expr, Parsing p) => (p :.: env) expr -> (p :.: env) expr
atom var
  =   lam var
  <|> parens (prd <$> sepBy (expr_ var) comma)
  <|> var
  where
  prd [] = S.unit
  prd ts = foldl1 (S.**) ts

app :: (Permutable env, S.App expr, Parsing p) => ((p :.: env) expr -> (p :.: env) expr) -> ((p :.: env) expr -> (p :.: env) expr)
app atom tvar = foldl (S.$$) <$> atom tvar <*> many (atom tvar)


identS, ident, tidentS, tident :: Parsing p => p S.Name
identS = (:) <$> lower <*> many letter
ident = token identS
tidentS = (:) <$> upper <*> many letter
tident = token tidentS

arrow :: Parsing p => p String
arrow = token (string "->")
