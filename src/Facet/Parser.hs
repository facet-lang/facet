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
import           Control.Selective
import           Data.Char (isSpace)
import           Data.Coerce
import           Data.Foldable (foldl')
import qualified Data.HashSet as HashSet
import           Data.Text (Text)
import           Facet.Name
import           Facet.Parser.Table
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


module' :: (Monad p, PositionParsing p) => Facet p S.Module
module' = locating $ S.module' <$> mname <* colon <* symbol "Module" <*> braces (many decl)

decl :: (Monad p, PositionParsing p) => Facet p S.Module
decl = locating
   $   S.defTerm <$> ename <* colon <*> tsig tglobal
   <|> S.defType <$> tname <* colon <*> tsig tglobal

tsigTable :: (Monad p, PositionParsing p) => Table (Facet p) S.Type S.Decl
tsigTable =
  [ [ Binder (forAll (liftA2 (S.>=>))) ]
  ]

sigTable :: (Monad p, PositionParsing p) => Facet p S.Type -> Table (Facet p) S.Expr S.Decl
sigTable tvars =
  [ [ Binder (binder tvars) ]
  ]

tsig :: (Monad p, PositionParsing p) => Facet p S.Type -> Facet p S.Decl
tsig = build tsigTable (\ _ vars -> sig vars global)

sig :: (Monad p, PositionParsing p) => Facet p S.Type -> Facet p S.Expr -> Facet p S.Decl
sig tvars = build (sigTable tvars) (\ _ vars -> (S..=) <$> monotype_ tvars <*> comp vars)

binder :: (Monad p, PositionParsing p) => Facet p S.Type -> BindParser (Facet p) S.Expr S.Decl
binder tvars BindCtx{ self, vars } = locating $ do
  (i, t) <- nesting $ (,) <$> try (symbolic '(' *> varPattern ename) <* colon <*> type_ tvars <* symbolic ')'
  bindVarPattern i $ \ v ext -> ((v S.::: t) S.>->) <$ arrow <*> self (ext vars)


typeTable :: (Monad p, PositionParsing p) => Table (Facet p) S.Type S.Type
typeTable = [ Binder (forAll (liftA2 (S.>~>))) ] : monotypeTable

monotypeTable :: (Monad p, PositionParsing p) => Table (Facet p) S.Type S.Type
monotypeTable =
  [ [ Infix R ((S.-->) <$ arrow) ]
  , [ Infix L (pure (S..$)) ]
  , [ -- FIXME: we should treat Unit & Type as globals.
      Atom (const (S._Unit <$ token (string "Unit")))
    , Atom (const (S._Type <$ token (string "Type")))
    , Atom id
    ]
  ]

forAll
  :: (S.Located res, Monad p, PositionParsing p)
  => (Facet p (Name S.::: S.Type) -> Facet p res -> Facet p res)
  -> BindParser (Facet p) S.Type res
forAll (>=>) BindCtx{ self, vars } = locating $ do
  (names, ty) <- braces ((,) <$> commaSep1 tname <* colon <*> type_ vars)
  let loop i rest vars = bind i $ \ v -> pure (v S.::: ty) >=> rest (S.tbound v <$ variable v <|> vars)
  arrow *> foldr loop self names vars

type' :: (Monad p, PositionParsing p) => Facet p S.Type
type' = type_ tglobal

type_ :: (Monad p, PositionParsing p) => Facet p S.Type -> Facet p S.Type
type_ = build typeTable (terminate parens (toBindParser (Infix L ((S..*) <$ comma))))

monotype_ :: (Monad p, PositionParsing p) => Facet p S.Type -> Facet p S.Type
monotype_ = build monotypeTable (terminate parens (toBindParser (Infix L ((S..*) <$ comma))))

tglobal :: (Monad p, TokenParsing p) => Facet p S.Type
tglobal = S.tglobal <$> tname <?> "variable"


exprTable :: (Monad p, PositionParsing p) => Table (Facet p) S.Expr S.Expr
exprTable =
  [ [ Infix L (pure (S.$$)) ]
  , [ Atom comp
    , Atom id
    ]
  ]

expr :: (Monad p, PositionParsing p) => Facet p S.Expr
expr = expr_ global

global :: (Monad p, TokenParsing p) => Facet p S.Expr
global = S.global <$> ename <?> "variable"

expr_ :: (Monad p, PositionParsing p) => Facet p S.Expr -> Facet p S.Expr
expr_ = build exprTable (terminate parens (toBindParser (Infix L ((S.**) <$ comma))))

comp :: (Monad p, PositionParsing p) => Facet p S.Expr -> Facet p S.Expr
comp = braces . build compTable (const expr_)

compTable :: (Monad p, PositionParsing p) => Table (Facet p) S.Expr S.Expr
compTable =
  [ [ Binder clause ]
  ]

clause :: (Monad p, PositionParsing p) => BindParser (Facet p) S.Expr S.Expr
clause = self . vars
  where
  self vars = (do
    patterns <- try (some ((,) <$> position <*> pattern) <* arrow)
    foldr clause expr_ patterns vars) <?> "clause"
  clause (start, p) rest vars = bindPattern p $ \ vs ext -> do
    lam <- foldr (fmap . S.lam) (rest (ext vars)) vs
    end <- position
    pure (S.locate (Span start end) lam)

bindPattern :: PositionParsing p => S.Pattern -> ([Name] -> (Facet p S.Expr -> Facet p S.Expr) -> Facet p S.Expr) -> Facet p S.Expr
bindPattern S.Wildcard   f = bind __ (\ v -> f [v] id)
bindPattern (S.Var n)    f = bind n  (\ v -> f [v] (S.bound v <$ variable v <|>))
bindPattern (S.Tuple ps) f = go [] id ps
  where
  go vs ext []     = f vs ext
  go vs ext (p:ps) = bindPattern p $ \ vs' ext' -> go (vs <> vs') (ext . ext') ps

bindVarPattern :: (PositionParsing p, Coercible t Text) => Maybe t -> (Name -> (Facet p S.Expr -> Facet p S.Expr) -> Facet p res) -> Facet p res
bindVarPattern Nothing  f = bind __ (\ v -> f v id)
bindVarPattern (Just n) f = bind n  (\ v -> f v (S.bound v <$ variable v <|>))


varPattern :: (Monad p, TokenParsing p) => p name -> p (Maybe name)
varPattern n = Just <$> n <|> Nothing <$ wildcard


wildcard :: (Monad p, TokenParsing p) => p ()
wildcard = reserve nameStyle "_"

-- FIXME: patterns
pattern :: (Monad p, TokenParsing p) => p S.Pattern
pattern =
  (   S.Var <$> ename
  <|> S.Wildcard <$ wildcard
  <|> S.Tuple <$> parens (commaSep pattern))
  <?> "pattern"


ename, _hname :: (Monad p, TokenParsing p) => p S.EName
ename  = ident nameStyle
_hname = ident hnameStyle
tname :: (Monad p, TokenParsing p) => p S.TName
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
variable v = token (text (hint v) *> notFollowedBy alphaNum)


locating :: (PositionParsing p, S.Located a) => p a -> p a
locating = fmap (uncurry S.locate) . spanned
