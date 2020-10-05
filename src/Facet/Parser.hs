{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Parser
( runFacet
, Facet(..)
, module'
, decl
, type'
, expr
, whole
) where

import           Control.Applicative (Alternative(..), liftA2)
import           Control.Carrier.Reader
import           Control.Lens (review)
import           Control.Selective
import           Data.Char (isSpace)
import           Data.Coerce
import           Data.Foldable (foldl')
import qualified Data.HashSet as HashSet
import           Data.Text (Text, unpack)
import           Facet.Name
import           Facet.Parser.Table
import qualified Facet.Surface.Decl as D
import qualified Facet.Surface.Expr as E
import qualified Facet.Surface.Module as M
import qualified Facet.Surface.Pattern as P
import qualified Facet.Surface.Type as T
import qualified Facet.Syntax as S
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


-- Modules

module' :: (Monad p, PositionParsing p) => Facet p M.Module
module' = locating $ M.module' <$> mname <* colon <* symbol "Module" <*> braces (many decl)

decl :: (Monad p, PositionParsing p) => Facet p M.Module
decl = locating
  $   M.defTerm <$> ename <* colon <*> tsig tglobal
  <|> M.defType <$> tname <* colon <*> tsig tglobal


-- Declarations

tsigTable :: (Monad p, PositionParsing p) => Table (Facet p) T.Type D.Decl
tsigTable =
  [ [ Binder (forAll (liftA2 (D.>=>))) ]
  ]

sigTable :: (Monad p, PositionParsing p) => Facet p T.Type -> Table (Facet p) E.Expr D.Decl
sigTable tvars =
  [ [ Binder (binder tvars) ]
  ]

tsig :: (Monad p, PositionParsing p) => Facet p T.Type -> Facet p D.Decl
tsig = build tsigTable (\ _ vars -> sig vars global)

sig :: (Monad p, PositionParsing p) => Facet p T.Type -> Facet p E.Expr -> Facet p D.Decl
sig tvars = build (sigTable tvars) (\ _ vars -> (D..=) <$> monotype_ tvars <*> comp vars)

binder :: (Monad p, PositionParsing p) => Facet p T.Type -> BindParser (Facet p) E.Expr D.Decl
binder tvars BindCtx{ self, vars } = locating $ do
  (i, t) <- nesting $ (,) <$> try (symbolic '(' *> varPattern ename) <* colon <*> type_ tvars <* symbolic ')'
  bindVarPattern i $ \ v ext -> ((v S.::: t) D.>->) <$ arrow <*> self (ext vars)


-- Types

typeTable :: (Monad p, PositionParsing p) => Table (Facet p) T.Type T.Type
typeTable = [ Binder (forAll (liftA2 (curry (review T._ForAll)))) ] : monotypeTable

monotypeTable :: (Monad p, PositionParsing p) => Table (Facet p) T.Type T.Type
monotypeTable =
  [ [ Infix R (curry (review T._Arrow) <$ arrow) ]
  , [ Infix L (pure (curry (review T._App))) ]
  , [ -- FIXME: we should treat Unit & Type as globals.
      Atom (const (T._Unit <$ token (string "Unit")))
    , Atom (const (T._Type <$ token (string "Type")))
    , Atom id
    ]
  ]

forAll
  :: (Located res, Monad p, PositionParsing p)
  => (Facet p (Name S.::: T.Type) -> Facet p res -> Facet p res)
  -> BindParser (Facet p) T.Type res
forAll (>=>) BindCtx{ self, vars } = locating $ do
  (names, ty) <- braces ((,) <$> commaSep1 tname <* colon <*> type_ vars)
  let loop i rest vars = bind i $ \ v -> pure (v S.::: ty) >=> rest (review T.bound_ v <$ variable v <|> vars)
  arrow *> foldr loop self names vars

type' :: (Monad p, PositionParsing p) => Facet p T.Type
type' = type_ tglobal

type_ :: (Monad p, PositionParsing p) => Facet p T.Type -> Facet p T.Type
type_ = build typeTable (terminate parens (toBindParser (Infix L (curry (review T._Prd) <$ comma))))

monotype_ :: (Monad p, PositionParsing p) => Facet p T.Type -> Facet p T.Type
monotype_ = build monotypeTable (terminate parens (toBindParser (Infix L (curry (review T._Prd) <$ comma))))

tglobal :: (Monad p, TokenParsing p) => Facet p T.Type
tglobal = review T.global_ <$> tname <?> "variable"


-- Expressions

exprTable :: (Monad p, PositionParsing p) => Table (Facet p) E.Expr E.Expr
exprTable =
  [ [ Infix L (pure (curry (review E._App))) ]
  , [ Atom comp
    , Atom (const (review E.hole_ <$> hname))
    , Atom id
    ]
  ]

expr :: (Monad p, PositionParsing p) => Facet p E.Expr
expr = expr_ global

global :: (Monad p, TokenParsing p) => Facet p E.Expr
global = review E.global_ <$> ename <?> "variable"

expr_ :: (Monad p, PositionParsing p) => Facet p E.Expr -> Facet p E.Expr
expr_ = build exprTable (terminate parens (toBindParser (Infix L (curry (review E._Prd) <$ comma))))

comp :: (Monad p, PositionParsing p) => Facet p E.Expr -> Facet p E.Expr
comp = braces . build compTable (const expr_)

compTable :: (Monad p, PositionParsing p) => Table (Facet p) E.Expr E.Expr
compTable =
  [ [ Binder clause ]
  ]

clause :: (Monad p, PositionParsing p) => BindParser (Facet p) E.Expr E.Expr
clause = self . vars
  where
  self vars = (do
    patterns <- try (some ((,) <$> position <*> pattern) <* arrow)
    foldr clause expr_ patterns vars) <?> "clause"
  clause (start, p) rest vars = bindPattern p $ \ vs ext -> do
    lam <- foldr (fmap . curry (review E._Lam)) (rest (ext vars)) vs
    end <- position
    pure (locate (Span start end) lam)


-- Patterns

bindPattern :: PositionParsing p => P.Pattern -> ([Name] -> (Facet p E.Expr -> Facet p E.Expr) -> Facet p E.Expr) -> Facet p E.Expr
bindPattern P.Wildcard   f = bind __ (\ v -> f [v] id)
bindPattern (P.Var n)    f = bind n  (\ v -> f [v] (review E.bound_ v <$ variable v <|>))
bindPattern (P.Tuple ps) f = go [] id ps
  where
  go vs ext []     = f vs ext
  go vs ext (p:ps) = bindPattern p $ \ vs' ext' -> go (vs <> vs') (ext . ext') ps

bindVarPattern :: (PositionParsing p, Coercible t Text) => Maybe t -> (Name -> (Facet p E.Expr -> Facet p E.Expr) -> Facet p res) -> Facet p res
bindVarPattern Nothing  f = bind __ (\ v -> f v id)
bindVarPattern (Just n) f = bind n  (\ v -> f v (review E.bound_ v <$ variable v <|>))


varPattern :: (Monad p, TokenParsing p) => p name -> p (Maybe name)
varPattern n = Just <$> n <|> Nothing <$ wildcard


wildcard :: (Monad p, TokenParsing p) => p ()
wildcard = reserve nameStyle "_"

-- FIXME: patterns
pattern :: (Monad p, TokenParsing p) => p P.Pattern
pattern =
  (   P.Var <$> ename
  <|> P.Wildcard <$ wildcard
  <|> P.Tuple <$> parens (commaSep pattern))
  <?> "pattern"


-- Names

ename :: (Monad p, TokenParsing p) => p E.EName
ename  = ident nameStyle

hname :: (Monad p, TokenParsing p) => p Text
hname = ident hnameStyle

tname :: (Monad p, TokenParsing p) => p T.TName
tname = ident tnameStyle

mname :: (Monad p, TokenParsing p) => p MName
mname = token (runUnspaced (foldl' (:.) . MName <$> comp <* dot <*> sepBy comp dot))
  where
  comp = ident tnameStyle

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
variable v = token (try (text (hint v) *> notFollowedBy alphaNum)) <?> unpack (hint v)


locating :: (PositionParsing p, Located a) => p a -> p a
locating = fmap (uncurry locate) . spanned
