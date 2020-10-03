{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Parser
( runFacet
, Facet(..)
, decl
, type'
, expr
, whole
) where

import           Control.Applicative (Alternative(..), liftA2, (<**>))
import           Control.Carrier.Reader
import           Control.Selective
import           Data.Char (isSpace)
import           Data.Coerce
import qualified Data.HashSet as HashSet
import           Data.Text (Text)
import           Facet.Name
import qualified Facet.Surface as S
import qualified Facet.Surface.Pattern as S
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

runFacet :: Int -> Facet m a -> m a
runFacet i (Facet m) = m i

bind :: Coercible t Text => t -> (Name -> Facet m a) -> Facet m a
bind n b = Facet $ \ i -> runFacet (i + 1) (b (Name (coerce n) i))

newtype Facet m a = Facet (Int -> m a)
  deriving (Alternative, Applicative, Functor, Monad, MonadFail) via ReaderC Int m

instance Selective m => Selective (Facet m) where
  select f a = Facet $ \ v -> select (runFacet v f) (runFacet v a)

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
  text    = lift . text

instance TokenParsing m => TokenParsing (Facet m) where
  someSpace = buildSomeSpaceParser (skipSome (satisfy isSpace)) emptyCommentStyle{ _commentLine = "#" }

instance PositionParsing p => PositionParsing (Facet p) where
  position = lift position

lift :: p a -> Facet p a
lift = Facet . const


whole :: TokenParsing p => p a -> p a
whole p = whiteSpace *> p <* eof


decl :: (S.Module expr ty decl mod, S.Located expr, S.Located ty, S.Located decl, S.Located mod, Monad p, PositionParsing p) => Facet p mod
decl = locating $ (S..:.) <$> dname <* colon <*> tsig tglobal

tsigTable :: (S.Decl expr ty decl, S.Located ty, S.Located decl, Monad p, PositionParsing p) => Table (Facet p) ty decl
tsigTable =
  [ [ Binder (forAll (liftA2 (S.>=>))) ]
  ]

sigTable :: (S.Decl expr ty decl, S.Located ty, S.Located decl, Monad p, PositionParsing p) => Facet p ty -> Table (Facet p) expr decl
sigTable tvars =
  [ [ Binder (binder tvars) ]
  ]

tsig :: (S.Decl expr ty decl, S.Located expr, S.Located ty, S.Located decl, Monad p, PositionParsing p) => Facet p ty -> Facet p decl
tsig = build tsigTable (\ _ vars -> sig vars global)

sig :: (S.Decl expr ty decl, S.Located expr, S.Located ty, S.Located decl, Monad p, PositionParsing p) => Facet p ty -> Facet p expr -> Facet p decl
sig tvars = build (sigTable tvars) (\ _ vars -> (S..=) <$> monotype_ tvars <*> expr_ vars)

binder :: (S.Decl expr ty decl, S.Located ty, S.Located decl, Monad p, PositionParsing p) => Facet p ty -> BindParser (Facet p) expr decl
binder tvars BindCtx{ self, vars } = locating $ do
  (i, t) <- nesting $ (,) <$> try (symbolic '(' *> varPattern ename) <* colon <*> type_ tvars <* symbolic ')'
  bindVarPattern i $ \ v ext -> ((v S.::: t) S.>->) <$ arrow <*> self (ext vars)


data BindCtx p a b = BindCtx
  { self :: p a -> p b
  , next :: p a -> p b
  , vars :: p a
  }

data ExprCtx p a = ExprCtx
  { self :: p a
  , next :: p a
  }

toExprCtx :: BindCtx p a b -> ExprCtx p b
toExprCtx BindCtx{ self, next, vars } = ExprCtx{ self = self vars, next = next vars }

data Assoc = N | L | R

data Operator p a b
  -- TODO: prefix, postfix, mixfix
  = Infix Assoc (p b -> p b) (p (b -> b -> b))
  | Binder (BindParser p a b)
  | Atom (p a -> p b)

toBindParser :: Parsing p => Operator p a b -> BindParser p a b
toBindParser = \case
  Infix N wrap op -> (\ ExprCtx{ next } -> wrap (try (next <**> op) <*> next)) . toExprCtx
  Infix L wrap op -> (\ ExprCtx{ next } -> chainl1_ next wrap op) . toExprCtx
  Infix R wrap op -> (\ ExprCtx{ self, next } -> wrap (try (next <**> op) <*> self)) . toExprCtx
  Binder p        -> p
  Atom p          -> p . vars

type BindParser p a b = BindCtx p a b -> p b
type Table p a b = [[Operator p a b]]

-- | Build a parser for a Table.
build :: Parsing p => Table p a b -> ((p a -> p b) -> (p a -> p b)) -> (p a -> p b)
build ts end = root
  where
  root = foldr chain (end root) ts
  chain ps next = self
    where
    self = foldr (\ p rest vars -> toBindParser p BindCtx{ self, next, vars } <|> rest vars) next ps

terminate :: (p b -> p b) -> BindParser p a b -> (p a -> p b) -> (p a -> p b)
terminate wrap op next = self where self vars = wrap $ op BindCtx{ next, self, vars }

typeTable :: (S.Type ty, S.Located ty, Monad p, PositionParsing p) => Table (Facet p) ty ty
typeTable = [ Binder (forAll (liftA2 (S.>~>))) ] : monotypeTable

monotypeTable :: (S.Type ty, S.Located ty, Monad p, PositionParsing p) => Table (Facet p) ty ty
monotypeTable =
  [ [ Infix R locating ((S.-->) <$ arrow) ]
  , [ Infix L locating (pure (S..$)) ]
  , [ -- FIXME: we should treat Unit & Type as globals.
      Atom (const (S._Unit <$ token (string "Unit")))
    , Atom (const (S._Type <$ token (string "Type")))
    , Atom id
    ]
  ]

forAll
  :: (S.Type ty, S.Located ty, S.Located res, Monad p, PositionParsing p)
  => (Facet p (Name S.::: ty) -> Facet p res -> Facet p res)
  -> BindParser (Facet p) ty res
forAll (>=>) BindCtx{ self, vars } = locating $ do
  (names, ty) <- braces ((,) <$> commaSep1 tname <* colon <*> type_ vars)
  let loop i rest vars = bind i $ \ v -> pure (v S.::: ty) >=> rest (S.tbound v <$ variable v <|> vars)
  arrow *> foldr loop self names vars

type' :: (S.Type ty, S.Located ty, Monad p, PositionParsing p) => Facet p ty
type' = type_ tglobal

type_ :: (S.Type ty, S.Located ty, Monad p, PositionParsing p) => Facet p ty -> Facet p ty
type_ = build typeTable (terminate parens (toBindParser (Infix L locating ((S..*) <$ comma))))

monotype_ :: (S.Type ty, S.Located ty, Monad p, PositionParsing p) => Facet p ty -> Facet p ty
monotype_ = build monotypeTable (terminate parens (toBindParser (Infix L locating ((S..*) <$ comma))))

tglobal :: (S.Type ty, Monad p, TokenParsing p) => Facet p ty
tglobal = S.tglobal <$> tname <?> "variable"


exprTable :: (S.Expr expr, S.Located expr, Monad p, PositionParsing p) => Table (Facet p) expr expr
exprTable =
  [ [ Infix L locating (pure (S.$$)) ]
  , [ Atom comp
    , Atom id
    ]
  ]

expr :: (S.Expr expr, S.Located expr, Monad p, PositionParsing p) => Facet p expr
expr = expr_ global

global :: (S.Expr expr, Monad p, TokenParsing p) => Facet p expr
global = S.global <$> ename <?> "variable"

expr_ :: (S.Expr expr, S.Located expr, Monad p, PositionParsing p) => Facet p expr -> Facet p expr
expr_ = build exprTable (terminate parens (toBindParser (Infix L locating ((S.**) <$ comma))))

comp :: (S.Expr expr, S.Located expr, Monad p, PositionParsing p) => Facet p expr -> Facet p expr
comp = braces . build compTable (const expr_)

compTable :: (S.Expr expr, S.Located expr, Monad p, PositionParsing p) => Table (Facet p) expr expr
compTable =
  [ [ Binder clause ]
  ]

clause :: (S.Expr expr, S.Located expr, Monad p, PositionParsing p) => BindParser (Facet p) expr expr
clause = self . vars
  where
  self vars = (do
    patterns <- try (some ((,) <$> position <*> pattern) <* arrow)
    foldr clause expr_ patterns vars) <?> "clause"
  clause (start, p) rest vars = bindPattern p $ \ v ext -> do
    lam <- S.lam v <$> rest (ext vars)
    end <- position
    pure (S.locate (Span start end) lam)

bindPattern :: (PositionParsing p, S.Expr expr) => S.Pattern -> (Name -> (Facet p expr -> Facet p expr) -> Facet p expr) -> Facet p expr
bindPattern S.Wildcard f = bind __ (\ v -> f v id)
bindPattern (S.Var n)  f = bind n  (\ v -> f v (S.bound v <$ variable v <|>))

bindVarPattern :: (PositionParsing p, S.Expr expr, Coercible t Text) => Maybe t -> (Name -> (Facet p expr -> Facet p expr) -> Facet p res) -> Facet p res
bindVarPattern Nothing  f = bind __ (\ v -> f v id)
bindVarPattern (Just n) f = bind n  (\ v -> f v (S.bound v <$ variable v <|>))


varPattern :: (Monad p, TokenParsing p) => p name -> p (Maybe name)
varPattern n = Just <$> n <|> Nothing <$ wildcard


wildcard :: (Monad p, TokenParsing p) => p ()
wildcard = reserve nameStyle "_"

-- FIXME: patterns
pattern :: (Monad p, TokenParsing p) => p S.Pattern
pattern
  =   S.Var <$> ename
  <|> S.Wildcard <$ wildcard


chainl1_ :: Alternative m => m a -> (m a -> m a) -> m (a -> a -> a) -> m a
chainl1_ p wrap op = go where go = wrap $ p <**> (flip <$> op <*> go <|> pure id)


ename, _hname :: (Monad p, TokenParsing p) => p S.EName
ename  = ident nameStyle
_hname = ident hnameStyle
tname :: (Monad p, TokenParsing p) => p S.TName
tname = ident tnameStyle
dname :: (Monad p, TokenParsing p) => p S.DName
dname = ident dnameStyle

reserved :: HashSet.HashSet String
reserved = HashSet.singleton "_"

nameLetter :: CharParsing p => p Char
nameLetter = alphaNum <|> char '_'

nameStyle :: CharParsing p => IdentifierStyle p
nameStyle = IdentifierStyle
  "name"
  (lower <|> char '_')
  nameLetter
  reserved
  Identifier
  ReservedIdentifier

dnameStyle :: CharParsing p => IdentifierStyle p
dnameStyle = IdentifierStyle
  "declaration name"
  (lower <|> char '_')
  nameLetter
  reserved
  Identifier
  ReservedIdentifier

tnameStyle :: CharParsing p => IdentifierStyle p
tnameStyle = IdentifierStyle
  "type name"
  upper
  nameLetter
  reserved
  Identifier
  ReservedIdentifier

hnameStyle :: CharParsing p => IdentifierStyle p
hnameStyle = IdentifierStyle
  "hole name"
  (char '?')
  nameLetter
  reserved
  Identifier
  ReservedIdentifier

arrow :: TokenParsing p => p String
arrow = symbol "->"

variable :: PositionParsing p => Name -> p ()
variable v = token (text (hint v) *> notFollowedBy alphaNum)


locating :: (PositionParsing p, S.Located a) => p a -> p a
locating = fmap (uncurry S.locate) . spanned
