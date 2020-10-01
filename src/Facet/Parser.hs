{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Parser
( runFacet
, Facet(..)
, decl
, type'
, expr
) where

import           Control.Applicative (Alternative(..), liftA2, (<**>))
import           Control.Carrier.Reader
import           Data.Char (isSpace)
import           Data.Coerce
import           Data.Text (Text)
import qualified Facet.Surface.Lifted as S
import           Prelude hiding (lines, null, span)
import           Text.Parser.Char
import           Text.Parser.Combinators
import           Text.Parser.Location
import           Text.Parser.Token
import           Text.Parser.Token.Highlight
import           Text.Parser.Token.Style

-- case
-- : (x : a) -> (f : a -> b) -> b
-- { f x }

-- TODO:
-- list literals
-- numeric literals
-- forcing nullary computations
-- holes

-- FIXME: a declaration whose body is a nullary computation backtracks all the way to a binding arrow type

runFacet :: Int -> Facet m a -> m a
runFacet i (Facet m) = m i

newtype Facet m a = Facet (Int -> m a)
  deriving (Alternative, Applicative, Functor, Monad) via ReaderC Int m

instance Parsing p => Parsing (Facet p) where
  try (Facet m) = Facet $ try . m
  Facet m <?> l = Facet $ \ e -> m e <?> l
  skipMany (Facet m) = Facet $ skipMany . m
  unexpected = lift . unexpected
  eof = lift eof
  notFollowedBy (Facet m) = Facet $ notFollowedBy . m

instance CharParsing p => CharParsing (Facet p) where
  satisfy = lift . satisfy
  char    = lift . char
  notChar = lift . notChar
  anyChar = lift anyChar
  string  = lift . string
  text = lift . text

instance TokenParsing m => TokenParsing (Facet m) where
  someSpace = buildSomeSpaceParser (skipSome (satisfy isSpace)) emptyCommentStyle{ _commentLine = "#" }

instance LocationParsing p => LocationParsing (Facet p) where
  position = lift position

lift :: p a -> Facet p a
lift = Facet . const


decl :: forall p expr ty decl mod . (S.Module expr ty decl mod, S.Located expr, S.Located ty, S.Located decl, S.Located mod, Monad p, LocationParsing p) => Facet p mod
decl = S.strengthen . locating $ fmap . (S..:.) <$> dname <* colon <*> sig global S.refl tglobal
  where
  sig :: Applicative env' => Facet p (env' expr) -> S.Extends env env' -> Facet p (env' ty) -> Facet p (env' decl)
  sig var _ tvar = try (bind var tvar) <|> forAll (S.>=>) (\ env -> sig (S.castF env var) env) tvar <|> liftA2 (S..=) <$> type_ tvar <*> expr_ var

  bind :: Applicative env' => Facet p (env' expr) -> Facet p (env' ty) -> Facet p (env' decl)
  bind var tvar = do
    (i, t) <- parens ((,) <$> name <* colon <*> type_ tvar)
    pure ((i S.:::) <$> t) S.>-> \ env t -> arrow *> sig (t <$ variable i <|> S.castF env var) S.refl (S.castF env tvar)


forAll
  :: forall env ty res p
  .  (Applicative env, S.Type ty, S.Located ty, S.Located res, Monad p, LocationParsing p)
  => (forall m env
     . (Applicative m, Applicative env)
     => m (env (S.TName S.::: ty))
     -> (forall env' . Applicative env' => S.Extends env env' -> env' ty -> m (env' res))
     -> m (env res))
  -> (forall env' . Applicative env' => S.Extends env env' -> Facet p (env' ty) -> Facet p (env' res))
  -> Facet p (env ty)
  -> Facet p (env res)
forAll (>=>) k tvar = locating $ do
  (names, ty) <- braces ((,) <$> commaSep1 tname <* colon <*> type_ tvar)
  let loop :: Applicative env' => S.Extends env env' -> Facet p (env' ty) -> Facet p (env' ty) -> [S.TName] -> Facet p (env' res)
      loop env ty tvar = \case
        []   -> k env tvar
        i:is -> (fmap (i S.:::) <$> ty) >=> \ env' t -> loop (env S.>>> env') (S.castF env' ty) (t <$ variable i <|> S.castF env' tvar) is
  arrow *> loop S.refl (pure ty) tvar names


type' :: (S.Type ty, S.Located ty, Monad p, LocationParsing p) => Facet p ty
type' = S.strengthen (type_ tglobal)

type_ :: (Applicative env, S.Type ty, S.Located ty, Monad p, LocationParsing p) => Facet p (env ty) -> Facet p (env ty)
type_ tvar = fn tvar <|> forAll (S.>~>) (const type_) tvar <?> "type"

fn :: (Applicative env, S.Type ty, S.Located ty, Monad p, LocationParsing p) => Facet p (env ty) -> Facet p (env ty)
fn tvar = locating $ app (S..$) tatom tvar <**> (flip (liftA2 (S.-->)) <$ arrow <*> fn tvar <|> pure id)

tatom :: (Applicative env, S.Type ty, S.Located ty, Monad p, LocationParsing p) => Facet p (env ty) -> Facet p (env ty)
tatom tvar = locating
  $   parens (prd <$> sepBy (type_ tvar) comma)
  -- FIXME: we should treat Unit & Type as globals.
  <|> pure S._Type <$ token (string "Unit")
  <|> pure S._Type <$ token (string "Type")
  <|> tvar
  where
  prd [] = pure S._Unit
  prd ts = foldl1 (liftA2 (S..*)) ts

tglobal :: (S.Type ty, Monad p, Applicative env, TokenParsing p) => Facet p (env ty)
tglobal = pure . S.tglobal <$> tname <?> "variable"


expr :: (S.Expr expr, S.Located expr, Monad p, LocationParsing p) => Facet p expr
expr = S.strengthen (expr_ global)

global :: (S.Expr expr, Monad p, Applicative env, TokenParsing p) => Facet p (env expr)
global = pure . S.global <$> name <?> "variable"

expr_ :: forall p env expr . (Applicative env, S.Expr expr, S.Located expr, Monad p, LocationParsing p) => Facet p (env expr) -> Facet p (env expr)
expr_ = app (S.$$) atom

-- FIXME: patterns
-- FIXME: nullary computations
lam :: forall p env expr . (Applicative env, S.Expr expr, S.Located expr, Monad p, LocationParsing p) => Facet p (env expr) -> Facet p (env expr)
lam var = braces $ clause var
  where
  clause :: Applicative env' => Facet p (env' expr) -> Facet p (env' expr)
  clause var = locating $ name >>= \ i -> S.lam0 (pure (pure i)) (\ env v -> let var' = v <$ variable i <|> S.castF env var in clause var' <|> arrow *> expr_ var') <?> "clause"

atom :: (Applicative env, S.Expr expr, S.Located expr, Monad p, LocationParsing p) => Facet p (env expr) ->Facet  p (env expr)
atom var = locating
  $   lam var
  <|> parens (prd <$> sepBy (expr_ var) comma)
  <|> var
  where
  prd [] = pure S.unit
  prd ts = foldl1 (liftA2 (S.**)) ts

app :: (Applicative env, LocationParsing p, S.Located expr) => (expr -> expr -> expr) -> (Facet p (env expr) -> Facet p (env expr)) -> (Facet p (env expr) -> Facet p (env expr))
app ($$) atom tvar = locating $ foldl (liftA2 ($$)) <$> atom tvar <*> many (atom tvar)


name, _hname :: (Monad p, TokenParsing p) => Facet p S.EName
name  = ident nameStyle
_hname = ident hnameStyle
tname :: (Monad p, TokenParsing p) => Facet p S.TName
tname = ident tnameStyle
dname :: (Monad p, TokenParsing p) => Facet p S.DName
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

arrow :: TokenParsing p => Facet p String
arrow = symbol "->"

variable :: (LocationParsing p, Coercible t Text) => t -> p ()
variable s = token (text (coerce s) *> notFollowedBy alphaNum)


locating :: (LocationParsing p, S.Located a, Functor env) => Facet p (env a) -> Facet p (env a)
locating = fmap (uncurry (fmap . S.locate)) . spanned
