{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
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
import           Facet.Name
import qualified Facet.Surface as S
import           Prelude hiding (lines, null, product, span)
import           Text.Parser.Char
import           Text.Parser.Combinators
import           Text.Parser.Position
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

bind :: (Monad m, Coercible t Text) => Facet m t -> (Name -> Facet m a) -> Facet m a
bind n b = n >>= \ n -> Facet $ \ i -> runFacet (i + 1) (b (Name (coerce n) i))

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

instance PositionParsing p => PositionParsing (Facet p) where
  position = lift position

lift :: p a -> Facet p a
lift = Facet . const


-- FIXME: de-stratify the grammar

decl :: forall p expr ty decl mod . (S.Module expr ty decl mod, S.Located expr, S.Located ty, S.Located decl, S.Located mod, Monad p, PositionParsing p) => Facet p mod
decl = locating $ (S..:.) <$> dname <* colon <*> sig global tglobal
  where
  sig :: Facet p expr -> Facet p ty -> Facet p decl
  sig var tvar = bind var tvar <|> forAll (liftA2 (S.>=>)) (sig var) tvar <|> (S..=) <$> fn tvar <*> expr_ var

  bind :: Facet p expr -> Facet p ty -> Facet p decl
  bind var tvar = do
    (i, t) <- nesting $ (,) <$> try (symbolic '(' *> name) <* colon <*> type_ tvar <* symbolic ')'
    Facet.Parser.bind (pure i) $ \ v -> ((v S.::: t) S.>->) <$ arrow <*> sig (S.bound v <$ variable i <|> var) tvar


forAll
  :: forall ty res p
  .  (S.Type ty, S.Located ty, S.Located res, Monad p, PositionParsing p)
  => (Facet p (Name S.::: ty) -> Facet p res -> Facet p res)
  -> (Facet p ty -> Facet p res)
  -> Facet p ty
  -> Facet p res
forAll (>=>) k tvar = locating $ do
  (names, ty) <- braces ((,) <$> commaSep1 tname <* colon <*> type_ tvar)
  let loop :: Facet p ty -> [S.TName] -> Facet p res
      loop tvar = \case
        []   -> k tvar
        i:is -> bind (pure i) $ \ v -> pure (v S.::: ty) >=> (loop (S.tbound v <$ variable i <|> tvar) is)
  arrow *> loop tvar names


data BindCtx p a b = BindCtx
  { self :: p a -> p b
  , next :: p a -> p b
  , vars :: p a
  }

-- | Operators are parsers parameterized by some expression context and the in-scope variables.
type Operator p a b = BindCtx p a b -> p b
type Table p a b = [[Operator p a b]]

-- | Build a parser for a Table.
build :: Alternative p => Table p a b -> ((p a -> p b) -> (p a -> p b)) -> (p a -> p b)
build ts end = root
  where
  root = foldr chain (end root) ts
  chain ps next = self
    where
    self = foldr (\ p rest vars -> p BindCtx{ self, next, vars } <|> rest vars) next ps

terminate :: TokenParsing p => Operator p a b -> (p a -> p b) -> (p a -> p b)
terminate op next = self where self vars = parens $ op BindCtx{ next, self, vars }

typeTable :: (S.Type ty, S.Located ty, Monad p, PositionParsing p) => Table (Facet p) ty ty
typeTable =
  [ [ fn', forAll' (liftA2 (S.>~>)) ]
  , [ app (S..$) ]
  , [ -- FIXME: we should treat Unit & Type as globals.
      const (S._Unit <$ token (string "Unit"))
    , const (S._Type <$ token (string "Type"))
    , vars
    ]
  ]

forAll'
  :: forall ty res p
  .  (S.Type ty, S.Located ty, S.Located res, Monad p, PositionParsing p)
  => (Facet p (Name S.::: ty) -> Facet p res -> Facet p res)
  -> Operator (Facet p) ty res
forAll' (>=>) BindCtx{ next, vars } = locating $ do
  (names, ty) <- braces ((,) <$> commaSep1 tname <* colon <*> type_ vars)
  let loop :: Facet p ty -> [S.TName] -> Facet p res
      loop vars = \case
        []   -> next vars
        i:is -> bind (pure i) $ \ v -> pure (v S.::: ty) >=> (loop (S.tbound v <$ variable i <|> vars) is)
  arrow *> loop vars names

fn' :: (S.Type ty, S.Located ty, PositionParsing p) => Operator p ty ty
fn' BindCtx{ self, next, vars } = locating $ next vars <**> (flip (S.-->) <$ arrow <*> self vars <|> pure id)

type' :: (S.Type ty, S.Located ty, Monad p, PositionParsing p) => Facet p ty
type' = type_ tglobal

type_ :: (S.Type ty, S.Located ty, Monad p, PositionParsing p) => Facet p ty -> Facet p ty
type_ = build typeTable (terminate (product (S..*)))

fn :: (S.Type ty, S.Located ty, Monad p, PositionParsing p) => Facet p ty -> Facet p ty
fn tvar = locating $ tapp tvar <**> (flip (S.-->) <$ arrow <*> fn tvar <|> pure id)
  where
  tapp vars = app (S..$) BindCtx{ self = tapp, next = tatom, vars }

tatom :: (S.Type ty, S.Located ty, Monad p, PositionParsing p) => Facet p ty -> Facet p ty
tatom tvar = locating
  $   parens (prd <$> sepBy (type_ tvar) comma)
  -- FIXME: we should treat Unit & Type as globals.
  <|> S._Unit <$ token (string "Unit")
  <|> S._Type <$ token (string "Type")
  <|> tvar
  where
  prd [] = S._Unit
  prd ts = foldl1 (S..*) ts

tglobal :: (S.Type ty, Monad p, TokenParsing p) => Facet p ty
tglobal = S.tglobal <$> tname <?> "variable"


exprTable :: (S.Expr expr, S.Located expr, Monad p, PositionParsing p) => Table (Facet p) expr expr
exprTable =
  [ [ app (S.$$) ]
  , [ lam'
    , vars
    ]
  ]

expr :: (S.Expr expr, S.Located expr, Monad p, PositionParsing p) => Facet p expr
expr = expr_ global

global :: (S.Expr expr, Monad p, TokenParsing p) => Facet p expr
global = S.global <$> name <?> "variable"

expr_ :: (S.Expr expr, S.Located expr, Monad p, PositionParsing p) => Facet p expr -> Facet p expr
expr_ vars = app (S.$$) BindCtx{ self = expr_, next = atom, vars }

-- FIXME: patterns
-- FIXME: nullary computations
lam' :: forall p expr . (S.Expr expr, S.Located expr, Monad p, PositionParsing p) => Operator (Facet p) expr expr
lam' = braces . clause
  where
  clause :: Operator (Facet p) expr expr
  clause BindCtx{ self, vars } = locating $ bind name $ \ v -> S.lam0 v <$> let var' = S.bound v <$ variable (hint v) <|> vars in self var' <|> arrow *> expr_ var' <?> "clause"

-- FIXME: patterns
-- FIXME: nullary computations
lam :: forall p expr . (S.Expr expr, S.Located expr, Monad p, PositionParsing p) => Facet p expr -> Facet p expr
lam var = braces $ clause var
  where
  clause :: Facet p expr -> Facet p expr
  clause var = locating $ bind name $ \ v -> S.lam0 v <$> let var' = S.bound v <$ variable (hint v) <|> var in clause var' <|> arrow *> expr_ var' <?> "clause"

atom :: (S.Expr expr, S.Located expr, Monad p, PositionParsing p) => Facet p expr -> Facet p expr
atom var = locating
  $   lam var
  <|> parens (prd <$> sepBy (expr_ var) comma)
  <|> var
  where
  prd [] = S.unit
  prd ts = foldl1 (S.**) ts

product :: (S.Located expr, PositionParsing p) => (expr -> expr -> expr) -> Operator p expr expr
product (**) BindCtx{ next, self, vars } = locating $ (**) <$> self vars <*> next vars

app :: (PositionParsing p, S.Located expr) => (expr -> expr -> expr) -> Operator p expr expr
app ($$) BindCtx{ next, vars } = locating $ next vars `chainl1` pure ($$)


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

variable :: (PositionParsing p, Coercible t Text) => t -> p ()
variable s = token (text (coerce s) *> notFollowedBy alphaNum)


locating :: (PositionParsing p, S.Located a) => p a -> p a
locating = fmap (uncurry S.locate) . spanned
