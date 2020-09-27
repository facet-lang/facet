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
import qualified Facet.Surface.Lifted as S
import           Prelude hiding (lines, null, span)
import           Text.Parser.Char
import           Text.Parser.Combinators
import           Text.Parser.Token
import           Text.Parser.Token.Highlight

-- case
-- : (x : a) -> (f : a -> b) -> b
-- { f x }

-- TODO:
-- list literals
-- numeric literals
-- forcing nullary computations
-- holes

decl :: forall p expr ty decl mod . (S.Module expr ty decl mod, Monad p, TokenParsing p) => p mod
decl = (S..:) <$> name <* colon <*> S.strengthen (sig (fmap pure global) S.refl (fmap pure tglobal))
  where
  sig :: Applicative env' => p (env' expr) -> S.Extends env env' -> p (env' ty) -> p (env' decl)
  sig var _ tvar = try (bind var tvar) <|> forAll (\ env -> sig (S.castF env var) env) tvar <|> liftA2 (S..=) <$> type_ tvar <*> expr_ var

  bind :: Applicative env' => p (env' expr) -> p (env' ty) -> p (env' decl)
  bind var tvar = do
    (i, t) <- parens ((,) <$> name <* colon <*> type_ tvar)
    pure t S.>-> \ env t -> arrow *> sig (t <$ variable i <|> S.castF env var) S.refl (S.castF env tvar)


forAll
  :: forall env ty res p
  .  (Applicative env, S.ForAll ty res, S.Type ty, Monad p, TokenParsing p)
  => (forall env' . Applicative env' => S.Extends env env' -> p (env' ty) -> p (env' res))
  -> p (env ty)
  -> p (env res)
forAll k tvar = do
  (names, ty) <- braces ((,) <$> commaSep1 tname <* colon <*> type_ tvar)
  let loop :: Applicative env' => S.Extends env env' -> p (env' ty) -> p (env' ty) -> [S.Name] -> p (env' res)
      loop env ty tvar = \case
        []   -> k env tvar
        i:is -> ty S.>=> \ env' t -> loop (env S.>>> env') (S.castF env' ty) (t <$ variable i <|> S.castF env' tvar) is
  arrow *> loop S.refl (pure ty) tvar names


type' :: (S.Type ty, Monad p, TokenParsing p) => p ty
type' = S.strengthen (type_ (fmap pure tglobal))

type_ :: (Applicative env, S.Type ty, Monad p, TokenParsing p) => p (env ty) -> p (env ty)
type_ tvar = fn tvar <|> forAll (const type_) tvar <?> "type"

fn :: (Applicative env, S.Type ty, Monad p, TokenParsing p) => p (env ty) -> p (env ty)
fn tvar = app (S..$) tatom tvar <**> (flip (liftA2 (S.-->)) <$ arrow <*> fn tvar <|> pure id)

tatom :: (Applicative env, S.Type ty, Monad p, TokenParsing p) => p (env ty) -> p (env ty)
tatom tvar
  =   parens (prd <$> sepBy (type_ tvar) comma)
  <|> tvar
  <|> pure S._Type <$ string "Type"
  where
  prd [] = pure S._Unit
  prd ts = foldl1 (liftA2 (S..*)) ts

tglobal :: (S.Type ty, Monad p, TokenParsing p) => p ty
tglobal = S.tglobal <$> tname <?> "variable"


expr :: (S.Expr expr, Monad p, TokenParsing p) => p expr
expr = S.strengthen (expr_ (pure <$> global))

global :: (S.Expr expr, Monad p, TokenParsing p) => p expr
global = S.global <$> name <?> "variable"

expr_ :: forall p env expr . (Applicative env, S.Expr expr, Monad p, TokenParsing p) => p (env expr) -> p (env expr)
expr_ = app (S.$$) atom

-- FIXME: patterns
-- FIXME: nullary computations
lam :: forall p env expr . (Applicative env, S.Expr expr, Monad p, TokenParsing p) => p (env expr) -> p (env expr)
lam var = braces $ clause var
  where
  clause :: Applicative env' => p (env' expr) -> p (env' expr)
  clause var = S.lam0 (\ env v -> name >>= \ i -> let var' = v <$ variable i <|> S.castF env var in clause var' <|> arrow *> expr_ var') <?> "clause"

atom :: (Applicative env, S.Expr expr, Monad p, TokenParsing p) => p (env expr) -> p (env expr)
atom var
  =   lam var
  <|> parens (prd <$> sepBy (expr_ var) comma)
  <|> var
  where
  prd [] = pure S.unit
  prd ts = foldl1 (liftA2 (S.**)) ts

app :: (Applicative env, TokenParsing p) => (expr -> expr -> expr) -> (p (env expr) -> p (env expr)) -> (p (env expr) -> p (env expr))
app ($$) atom tvar = foldl (liftA2 ($$)) <$> atom tvar <*> many (atom tvar)


name, tname, _holeName :: (Monad p, TokenParsing p) => p S.Name
name  = ident nameStyle
tname = ident tnameStyle
_holeName = ident holeNameStyle

nameStyle :: CharParsing p => IdentifierStyle p
nameStyle = IdentifierStyle
  "name"
  (lower <|> char '_')
  alphaNum
  mempty
  Identifier
  ReservedIdentifier

tnameStyle :: CharParsing p => IdentifierStyle p
tnameStyle = IdentifierStyle
  "type name"
  upper
  alphaNum
  mempty
  Identifier
  ReservedIdentifier

holeNameStyle :: CharParsing p => IdentifierStyle p
holeNameStyle = IdentifierStyle
  "hole name"
  (char '?')
  alphaNum
  mempty
  Identifier
  ReservedIdentifier

arrow :: TokenParsing p => p String
arrow = symbol "->"

variable :: TokenParsing p => String -> p String
variable s = token (string s <* notFollowedBy alphaNum)
