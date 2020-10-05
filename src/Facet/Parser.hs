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
import qualified Data.Map as Map
import           Data.Text (Text)
import           Facet.Name as N hiding (Assoc(..), Op(..))
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

type EEnv = Map.Map Text E.Expr
type TEnv = Map.Map Text T.Type

runFacet :: Int -> EEnv -> TEnv -> Facet m a -> m a
runFacet i e t (Facet m) = m i e t

bind :: Coercible t Text => t -> (Name -> Facet m a) -> Facet m a
bind n b = Facet $ \ i e t -> runFacet (i + 1) e t (b (Name (coerce n) i))

newtype Facet m a = Facet (Int -> EEnv -> TEnv -> m a)
  deriving (Alternative, Applicative, Functor, Monad, MonadFail) via ReaderC Int (ReaderC EEnv (ReaderC TEnv m))

instance Selective m => Selective (Facet m) where
  select f a = Facet $ \ v e t -> select (runFacet v e t f) (runFacet v e t a)

instance Parsing p => Parsing (Facet p) where
  try (Facet m) = Facet $ \ v e t -> try (m v e t)
  Facet m <?> l = Facet $ \ v e t -> m v e t <?> l
  skipMany (Facet m) = Facet $ \ v e t -> skipMany (m v e t)
  unexpected = lift . unexpected
  eof = lift eof
  notFollowedBy (Facet m) = Facet $ \ v e t -> notFollowedBy (m v e t)

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
lift = Facet . const . const . const


whole :: TokenParsing p => p a -> p a
whole p = whiteSpace *> p <* eof


-- Modules

module' :: (Monad p, PositionParsing p) => Facet p M.Module
module' = spanning $ M.module' <$> mname <* colon <* symbol "Module" <*> braces (many decl)

decl :: (Monad p, PositionParsing p) => Facet p M.Module
decl = spanning
  $   M.defTerm <$> ename <* colon <*> sig
  <|> M.defType <$> tname <* colon <*> sig


-- Declarations

sigTable :: (Monad p, PositionParsing p) => Table (Facet p) D.Decl
sigTable =
  [ [ Binder (forAll (liftA2 (D.>=>))) ]
  , [ Binder binder ]
  ]

sig :: (Monad p, PositionParsing p) => Facet p D.Decl
sig = build sigTable (const ((D..=) <$> monotype <*> comp))

binder :: (Monad p, PositionParsing p) => BindParser (Facet p) D.Decl
binder BindCtx{ self } = spanning $ do
  (i, t) <- nesting $ (,) <$> try (symbolic '(' *> varPattern ename) <* colon <*> type' <* symbolic ')'
  bindVarPattern i $ \ v -> ((v S.::: t) D.>->) <$ arrow <*> self


-- Types

typeTable :: (Monad p, PositionParsing p) => Table (Facet p) T.Type
typeTable = [ Binder (forAll (liftA2 (curry (review T.forAll_)))) ] : monotypeTable

monotypeTable :: (Monad p, PositionParsing p) => Table (Facet p) T.Type
monotypeTable =
  [ [ Infix R (curry (review T.arrow_) <$ arrow) ]
  , [ Infix L (pure (curry (review T.app_))) ]
  , [ -- FIXME: we should treat Unit & Type as globals.
      Atom (T._Unit <$ token (string "Unit"))
    , Atom (T._Type <$ token (string "Type"))
    , Atom tvar
    ]
  ]

forAll
  :: (Spanned res, Monad p, PositionParsing p)
  => (Facet p (Name S.::: T.Type) -> Facet p res -> Facet p res)
  -> BindParser (Facet p) res
forAll (>=>) BindCtx{ self } = spanning $ do
  (names, ty) <- braces ((,) <$> commaSep1 tname <* colon <*> type')
  let loop i rest = bind i $ \ v -> pure (v S.::: ty) >=> rest
  arrow *> foldr loop self names

type' :: (Monad p, PositionParsing p) => Facet p T.Type
type' = build typeTable (terminate parens (toBindParser (Infix L (curry (review T.prd_) <$ comma))))

monotype :: (Monad p, PositionParsing p) => Facet p T.Type
monotype = build monotypeTable (terminate parens (toBindParser (Infix L (curry (review T.prd_) <$ comma))))

tvar :: (Monad p, TokenParsing p) => Facet p T.Type
tvar = review T.global_ <$> tname <?> "variable"


-- Expressions

exprTable :: (Monad p, PositionParsing p) => Table (Facet p) E.Expr
exprTable =
  [ [ Infix L (pure (curry (review E.app_))) ]
  , [ Atom comp
    , Atom (review E.hole_ <$> hname)
    , Atom evar
    ]
  ]

expr :: (Monad p, PositionParsing p) => Facet p E.Expr
expr = build exprTable (terminate parens (toBindParser (Infix L (curry (review E.prd_) <$ comma))))

comp :: (Monad p, PositionParsing p) => Facet p E.Expr
comp = braces $ build compTable (const expr)

compTable :: (Monad p, PositionParsing p) => Table (Facet p) E.Expr
compTable =
  [ [ Binder clause ]
  ]

clause :: (Monad p, PositionParsing p) => BindParser (Facet p) E.Expr
clause _ = self
  where
  self = (do
    patterns <- try (some ((,) <$> position <*> pattern) <* arrow)
    foldr clause expr patterns) <?> "clause"
  clause (start, p) rest = bindPattern p $ \ vs -> do
    lam <- foldr (fmap . curry (review E.lam_)) rest vs
    end <- position
    pure (setSpan (Span start end) lam)

evar :: (Monad p, PositionParsing p) => Facet p E.Expr
evar = spanning $ review E.global_ <$> ename <?> "variable"


-- Patterns

bindPattern :: PositionParsing p => P.Pattern -> ([Name] -> Facet p E.Expr) -> Facet p E.Expr
bindPattern P.Wildcard   f = bind __ (\ v -> f [v])
bindPattern (P.Var n)    f = bind n  (\ v -> f [v])
-- FIXME: this is incorrect since the structure doesn’t get used in the clause
bindPattern (P.Tuple ps) f = go [] ps
  where
  go vs []     = f vs
  go vs (p:ps) = bindPattern p $ \ vs' -> go (vs <> vs') ps
bindPattern (P.Loc _ p) f = bindPattern p f

bindVarPattern :: Coercible t Text => Maybe t -> (Name -> Facet p res) -> Facet p res
bindVarPattern Nothing  = bind __
bindVarPattern (Just n) = bind n


varPattern :: (Monad p, TokenParsing p) => p name -> p (Maybe name)
varPattern n = Just <$> n <|> Nothing <$ wildcard


wildcard :: (Monad p, TokenParsing p) => p ()
wildcard = reserve enameStyle "_"

-- FIXME: patterns
pattern :: (Monad p, PositionParsing p) => p P.Pattern
pattern = spanning
  $   P.Var <$> ename
  <|> P.Wildcard <$ wildcard
  <|> P.Tuple <$> parens (commaSep pattern)
  <?> "pattern"


-- Names

ename :: (Monad p, TokenParsing p) => p N.EName
ename  = ident enameStyle

hname :: (Monad p, TokenParsing p) => p Text
hname = ident hnameStyle

tname :: (Monad p, TokenParsing p) => p N.TName
tname = ident tnameStyle

mname :: (Monad p, TokenParsing p) => p MName
mname = token (runUnspaced (foldl' (:.) . MName <$> comp <* dot <*> sepBy comp dot))
  where
  comp = ident tnameStyle

reserved :: HashSet.HashSet String
reserved = HashSet.singleton "_"

nameLetter :: CharParsing p => p Char
nameLetter = alphaNum <|> char '_'

enameStyle :: CharParsing p => IdentifierStyle p
enameStyle = IdentifierStyle
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
