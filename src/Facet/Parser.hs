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
import           Data.Coerce
import           Data.Text (Text)
import qualified Facet.Surface.Lifted as S
import           Prelude hiding (lines, null, span)
import           Text.Parser.Char
import           Text.Parser.Combinators
import           Text.Parser.Location
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

decl :: forall p expr ty decl mod . (S.Module expr ty decl mod, S.Located expr, S.Located ty, Monad p, LocationParsing p) => p mod
decl = (S..:) <$> dname <* colon <*> S.strengthen (sig (fmap pure global) S.refl (fmap pure tglobal))
  where
  sig :: Applicative env' => p (env' expr) -> S.Extends env env' -> p (env' ty) -> p (env' decl)
  sig var _ tvar = try (bind var tvar) <|> forAll (\ env -> sig (S.castF env var) env) tvar <|> liftA2 (S..=) <$> type_ tvar <*> expr_ var

  bind :: Applicative env' => p (env' expr) -> p (env' ty) -> p (env' decl)
  bind var tvar = do
    (i, t) <- parens ((,) <$> name <* colon <*> type_ tvar)
    pure ((i S.:::) <$> t) S.>-> \ env t -> arrow *> sig (fmap . S.locate <$> variable i <*> pure t <|> S.castF env var) S.refl (S.castF env tvar)


forAll
  :: forall env ty res p
  .  (Applicative env, S.ForAll ty res, S.Type ty, S.Located ty, Monad p, LocationParsing p)
  => (forall env' . Applicative env' => S.Extends env env' -> p (env' ty) -> p (env' res))
  -> p (env ty)
  -> p (env res)
forAll k tvar = do
  (names, ty) <- braces ((,) <$> commaSep1 tname <* colon <*> type_ tvar)
  let loop :: Applicative env' => S.Extends env env' -> p (env' ty) -> p (env' ty) -> [S.TName] -> p (env' res)
      loop env ty tvar = \case
        []   -> k env tvar
        i:is -> (fmap (i S.:::) <$> ty) S.>=> \ env' t -> loop (env S.>>> env') (S.castF env' ty) (t <$ variable i <|> S.castF env' tvar) is
  arrow *> loop S.refl (pure ty) tvar names


type' :: (S.Type ty, S.Located ty, Monad p, LocationParsing p) => p ty
type' = S.strengthen (type_ (fmap pure tglobal))

type_ :: (Applicative env, S.Type ty, S.Located ty, Monad p, LocationParsing p) => p (env ty) -> p (env ty)
type_ tvar = fn tvar <|> forAll (const type_) tvar <?> "type"

fn :: (Applicative env, S.Type ty, S.Located ty, Monad p, LocationParsing p) => p (env ty) -> p (env ty)
fn tvar = app (S..$) tatom tvar <**> (flip (liftA2 (S.-->)) <$ arrow <*> fn tvar <|> pure id)

tatom :: (Applicative env, S.Type ty, S.Located ty, Monad p, LocationParsing p) => p (env ty) -> p (env ty)
tatom tvar
  =   parens (prd <$> sepBy (type_ tvar) comma)
  <|> tvar
  where
  prd [] = pure S._Unit
  prd ts = foldl1 (liftA2 (S..*)) ts

tglobal :: (S.Type ty, Monad p, TokenParsing p) => p ty
tglobal = S.tglobal <$> tname <?> "variable"


expr :: (S.Expr expr, S.Located expr, Monad p, LocationParsing p) => p expr
expr = S.strengthen (expr_ (pure <$> global))

global :: (S.Expr expr, Monad p, TokenParsing p) => p expr
global = S.global <$> name <?> "variable"

expr_ :: forall p env expr . (Applicative env, S.Expr expr, S.Located expr, Monad p, LocationParsing p) => p (env expr) -> p (env expr)
expr_ = app (S.$$) atom

-- FIXME: patterns
-- FIXME: nullary computations
lam :: forall p env expr . (Applicative env, S.Expr expr, S.Located expr, Monad p, LocationParsing p) => p (env expr) -> p (env expr)
lam var = braces $ clause var
  where
  clause :: Applicative env' => p (env' expr) -> p (env' expr)
  clause var = name >>= \ i -> S.lam0 (pure (pure i)) (\ env v -> let var' = v <$ variable i <|> S.castF env var in clause var' <|> arrow *> expr_ var') <?> "clause"

atom :: (Applicative env, S.Expr expr, S.Located expr, Monad p, LocationParsing p) => p (env expr) -> p (env expr)
atom var
  =   lam var
  <|> parens (prd <$> sepBy (expr_ var) comma)
  <|> var
  where
  prd [] = pure S.unit
  prd ts = foldl1 (liftA2 (S.**)) ts

app :: (Applicative env, TokenParsing p) => (expr -> expr -> expr) -> (p (env expr) -> p (env expr)) -> (p (env expr) -> p (env expr))
app ($$) atom tvar = foldl (liftA2 ($$)) <$> atom tvar <*> many (atom tvar)


name, _hname :: (Monad p, TokenParsing p) => p S.EName
name  = ident nameStyle
_hname = ident hnameStyle
tname :: (Monad p, TokenParsing p) => p S.TName
tname = ident tnameStyle
dname :: (Monad p, TokenParsing p) => p S.DName
dname = ident dnameStyle

nameStyle :: CharParsing p => IdentifierStyle p
nameStyle = IdentifierStyle
  "name"
  (lower <|> char '_')
  alphaNum
  mempty
  Identifier
  ReservedIdentifier

dnameStyle :: CharParsing p => IdentifierStyle p
dnameStyle = IdentifierStyle
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

hnameStyle :: CharParsing p => IdentifierStyle p
hnameStyle = IdentifierStyle
  "hole name"
  (char '?')
  alphaNum
  mempty
  Identifier
  ReservedIdentifier

arrow :: TokenParsing p => p String
arrow = symbol "->"

variable :: (LocationParsing p, Coercible t Text) => t -> p Span
variable s = spanning (token (text (coerce s) <* notFollowedBy alphaNum))


locating :: (LocationParsing p, S.Located a, Functor env) => p (env a) -> p (env a)
locating = fmap (uncurry (fmap . S.locate)) . spanned
