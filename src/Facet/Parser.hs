{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TypeApplications #-}
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

import           Control.Applicative (Alternative(..))
import           Control.Carrier.Reader
import           Control.Selective
import           Data.Bool (bool)
import           Data.Char (isSpace)
import qualified Data.CharSet as CharSet
import qualified Data.CharSet.Unicode as Unicode
import           Data.Coerce (Coercible, coerce)
import           Data.Foldable (foldl')
import qualified Data.HashSet as HashSet
import           Data.List (elemIndex)
import qualified Data.List.NonEmpty as NE
import           Data.Text (Text, pack)
import qualified Facet.Name as N
import           Facet.Parser.Table as Op
import qualified Facet.Surface as S
import qualified Facet.Syntax as S
import           Prelude hiding (lines, null, product, span)
import           Text.Parser.Char
import           Text.Parser.Combinators
import           Text.Parser.Position
import           Text.Parser.Token
import           Text.Parser.Token.Highlight as Highlight
import           Text.Parser.Token.Style

-- case
-- : (x : a) -> (f : a -> b) -> b
-- { f x }

-- TODO:
-- list literals
-- numeric literals
-- forcing nullary computations

runFacet :: [N.UName] -> Facet m a -> m a
runFacet env (Facet m) = m env

bind :: Coercible t N.UName => t -> (N.UName -> Facet m a) -> Facet m a
bind n b = Facet $ \ env -> let n' = coerce n in runFacet (n':env) (b n')

resolve :: Coercible t N.UName => t -> [N.UName] -> (Either t N.Index)
resolve n = maybe (Left n) (Right . N.Index) . elemIndex @N.UName (coerce n)

env :: Applicative m => Facet m [N.UName]
env = Facet pure

newtype Facet m a = Facet ([N.UName] -> m a)
  deriving (Alternative, Applicative, Functor, Monad, MonadFail) via ReaderC [N.UName] m

instance Selective m => Selective (Facet m) where
  select f a = Facet $ \ env -> select (runFacet env f) (runFacet env a)

instance Parsing p => Parsing (Facet p) where
  try (Facet m) = Facet $ \ env -> try (m env)
  Facet m <?> l = Facet $ \ env -> m env <?> l
  skipMany (Facet m) = Facet $ \ env -> skipMany (m env)
  unexpected = lift . unexpected
  eof = lift eof
  notFollowedBy (Facet m) = Facet $ \ env -> notFollowedBy (m env)

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

-- FIXME: preserve comments; maybe replace Spanned with something that can capture comments.
module' :: (Monad p, PositionParsing p) => Facet p (Spanned S.Module)
module' = spanned (S.Module <$> mname <* colon <* symbol "Module" <*> pure [] <*> braces (many decl))


-- Declarations

decl :: (Monad p, PositionParsing p) => Facet p (Spanned (N.DName, Spanned S.Decl))
decl = spanned
  $   (,) <$> dename <* colon <*> spanned (S.TDecl <$> sig S.TDForAll (N.getEName <$> ename) (S.TDBody <$> monotype <*> comp))
  <|> (,) <$> dtname <* colon <*> spanned (S.DDecl <$> sig S.DDForAll (N.getTName <$> tname) (S.DDBody <$> monotype <*> braces (commaSep con)))


sig
  :: (Monad p, PositionParsing p)
  => ((S.Pl_ N.UName S.::: Spanned S.Type) -> Spanned res -> res)
  -> Facet p N.UName
  -> Facet p res
  -> Facet p (Spanned res)
sig (-->) name body = go
  where
  go = forAll (-->) go <|> binder (-->) name go <|> spanned body

binder
  :: (Monad p, PositionParsing p)
  => ((S.Pl_ N.UName S.::: Spanned S.Type) -> Spanned res -> res)
  -> Facet p N.UName
  -> Facet p (Spanned res)
  -> Facet p (Spanned res)
binder (-->) name k = do
  ((start, i), t) <- nesting $ (,) <$> try ((,) <$> position <* lparen <*> (coerce <$> name <|> N.__ <$ wildcard) <* colon) <*> type' <* rparen
  bind i $ \ v -> mk start (S.ex v S.::: t) <$ arrow <*> k <*> position
  where
  mk start t b end = (Span start end, t --> b)

con :: (Monad p, PositionParsing p) => Facet p (Spanned (N.CName S.::: Spanned S.Type))
con = spanned ((S.:::) <$> cname <* colon <*> type')


-- Types

monotypeTable :: (Monad p, PositionParsing p) => Table (Facet p) (Spanned S.Type)
monotypeTable =
  [ [ Infix R (pack "->") (\ s -> fmap ((,) s) . (S.:->)) ]
  , [ Infix L mempty (\ s -> fmap ((,) s) . (S.:$$)) ]
  , [ -- FIXME: we should treat this as a global.
      Atom (spanned (S.Type <$ token (string "Type")))
    , Atom tvar
    ]
  ]

forAll
  :: (Monad p, PositionParsing p)
  => ((S.Pl_ N.UName S.::: Spanned S.Type) -> Spanned res -> res)
  -> Facet p (Spanned res) -> Facet p (Spanned res)
forAll mk k = do
  start <- position
  (names, ty) <- braces ((,) <$> commaSep1 tname <* colon <*> type')
  arrow *> foldr (loop start ty) k names
  where
  loop start ty i rest = bind i $ \ v -> mk' start (S.im v S.::: ty) <$> rest <*> position
  mk' start t b end = (Span start end, mk t b)

type' :: (Monad p, PositionParsing p) => Facet p (Spanned S.Type)
type' = forAll (\ (n S.::: _T) b -> S.out n S.::: _T S.:=> b) type' <|> monotype

monotype :: (Monad p, PositionParsing p) => Facet p (Spanned S.Type)
monotype = build monotypeTable parens

tvar :: (Monad p, PositionParsing p) => Facet p (Spanned S.Type)
tvar = token (spanned (runUnspaced (fmap (either (S.TFree . N.T) (S.TBound)) . resolve <$> tname <*> Unspaced env <?> "variable")))


-- Expressions

exprTable :: (Monad p, PositionParsing p) => Table (Facet p) (Spanned S.Expr)
exprTable =
  [ [ Infix L mempty (\ s -> fmap ((,) s) . (S.:$)) ]
  , [ Atom comp
    , Atom (spanned (S.Hole <$> hname))
    , Atom evar
    ]
  ]

expr :: (Monad p, PositionParsing p) => Facet p (Spanned S.Expr)
expr = build exprTable parens

comp :: (Monad p, PositionParsing p) => Facet p (Spanned S.Expr)
-- NB: We parse sepBy1 and the empty case separately so that it doesn’t succeed at matching 0 clauses and then expect a closing brace when it sees a nullary computation
comp = spanned (S.Comp <$> spanned (braces (S.Clauses <$> sepBy1 clause comma <|> S.Expr <$> expr <|> pure (S.Clauses []))))

clause :: (Monad p, PositionParsing p) => Facet p (NE.NonEmpty (Spanned S.Pattern), Spanned S.Expr)
clause = (do
  ps <- try (NE.some1 pattern <* arrow)
  b' <- foldr (bindPattern . snd) expr ps
  pure (ps, b')) <?> "clause"

evar :: (Monad p, PositionParsing p) => Facet p (Spanned S.Expr)
evar
  =   token (spanned (runUnspaced (fmap (either (S.Free . N.E) S.Bound) . resolve <$> ename <*> Unspaced env <?> "variable")))
  <|> try (token (spanned (runUnspaced (S.Free . N.O <$> Unspaced (parens oname))))) -- FIXME: would be better to commit once we see a placeholder, but try doesn’t really let us express that


-- Patterns

bindPattern :: PositionParsing p => S.Pattern -> Facet p a -> Facet p a
bindPattern p m = case p of
  S.PVar n    -> bind n (const m)
  S.PCon _ ps -> foldr (bindPattern . snd) m ps


wildcard :: (Monad p, TokenParsing p) => p ()
wildcard = reserve enameStyle "_"

pattern :: (Monad p, PositionParsing p) => p (Spanned S.Pattern)
pattern = spanned
  $   S.PVar . N.getEName <$> ename
  <|> S.PVar N.__         <$  wildcard
  <|> try (parens (S.PCon <$> cname <*> many pattern))
  <?> "pattern"


-- Names

ename :: (Monad p, TokenParsing p) => p N.EName
ename  = ident enameStyle

oname :: (Monad p, TokenParsing p) => p N.Op
oname
  =   postOrIn <$ place <*> comp <*> option False (True <$ place)
  <|> try (outOrPre <$> comp <* place) <*> optional comp
  where
  place = wildcard
  comp = ident onameStyle
  outOrPre s e = maybe (N.Prefix s) (N.Outfix s) e
  -- FIXME: how should we specify associativity?
  postOrIn c = bool (N.Postfix c) (N.Infix N.N c)

_onameN :: (Monad p, TokenParsing p) => p N.OpN
_onameN
  =   postOrIn <$ place <*> sepByNonEmpty comp place <*> option False (True <$ place)
  <|> try (uncurry . outOrPre <$> comp <* place) <*> ((,) <$> sepBy1 comp place <*> option False (True <$ place) <|> pure ([], True))
  where
  place = wildcard
  comp = ident onameStyle
  outOrPre c cs = bool (N.OutfixN c (init cs) (last cs)) (N.PrefixN c cs)
  -- FIXME: how should we specify associativity?
  postOrIn cs = bool (N.PostfixN (NE.init cs) (NE.last cs)) (N.InfixN N.N cs)

hname :: (Monad p, TokenParsing p) => p Text
hname = ident hnameStyle

cname :: (Monad p, TokenParsing p) => p N.CName
cname = ident cnameStyle

tname :: (Monad p, TokenParsing p) => p N.TName
tname = ident tnameStyle

dename :: (Monad p, TokenParsing p) => p N.DName
dename  = N.E <$> ename <|> N.O <$> oname

dtname :: (Monad p, TokenParsing p) => p N.DName
dtname  = N.T <$> tname

mname :: (Monad p, TokenParsing p) => p N.MName
mname = token (runUnspaced (foldl' (N.:.) . N.MName <$> comp <* dot <*> sepBy comp dot))
  where
  comp = ident tnameStyle

qname :: (Monad p, TokenParsing p) => p N.QName
qname = runUnspaced (fmap (N.:.:) . foldl' (N.:.) . N.MName <$> comp <* dot <*> many (comp <* dot) <*> (dename <|> dtname))
  where
  comp = ident tnameStyle


reserved :: HashSet.HashSet String
reserved = HashSet.singleton "_"

nameChar :: CharParsing p => p Char
nameChar = alphaNum <|> char '_'

opChar :: CharParsing p => p Char
opChar = oneOfSet (CharSet.difference (Unicode.punctuation <> Unicode.symbol) (CharSet.fromList "(){}"))

enameStyle :: CharParsing p => IdentifierStyle p
enameStyle = IdentifierStyle
  "name"
  (lower <|> char '_')
  nameChar
  reserved
  Identifier
  ReservedIdentifier

onameStyle :: CharParsing p => IdentifierStyle p
onameStyle = IdentifierStyle
  "operator"
  opChar
  opChar
  mempty
  Highlight.Operator
  ReservedOperator

cnameStyle :: CharParsing p => IdentifierStyle p
cnameStyle = IdentifierStyle
  "constructor name"
  lower
  nameChar
  reserved
  Identifier
  ReservedIdentifier

tnameStyle :: CharParsing p => IdentifierStyle p
tnameStyle = IdentifierStyle
  "type name"
  upper
  nameChar
  reserved
  Identifier
  ReservedIdentifier

hnameStyle :: CharParsing p => IdentifierStyle p
hnameStyle = IdentifierStyle
  "hole name"
  (char '?')
  nameChar
  reserved
  Identifier
  ReservedIdentifier

arrow :: TokenParsing p => p String
arrow = symbol "->"

lparen :: TokenParsing p => p Char
lparen = symbolic '('

rparen :: TokenParsing p => p Char
rparen = symbolic ')'
