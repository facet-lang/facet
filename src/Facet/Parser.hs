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
import           Control.Lens (review)
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
import qualified Facet.Surface.Comp as C
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

module' :: (Monad p, PositionParsing p) => Facet p (M.Module Span)
module' = mk <$> spanned ((,) <$> mname <* colon <* symbol "Module" <*> braces (many decl))
  where
  mk (s, (n, ds)) = M.Module s n ds

decl :: (Monad p, PositionParsing p) => Facet p (M.Def Span)
decl = mk <$> spanned ((,) <$> dname <* colon <*> sig)
  where
  mk (s, (n, b)) = M.Def s n b


-- Declarations

sigTable :: (Monad p, PositionParsing p) => Table (Facet p) D.Decl
sigTable =
  [ [ Op.Operator (forAll (D.:=>)) ]
  , [ Op.Operator binder ]
  ]

sig :: (Monad p, PositionParsing p) => Facet p D.Decl
sig = build sigTable (const (settingSpan (review D.def_ <$> ((,) <$> monotype <*> comp)))) -- FIXME: parse type declarations too

binder :: (Monad p, PositionParsing p) => OperatorParser (Facet p) D.Decl
binder self _ = do
  ((start, i), t) <- nesting $ (,) <$> try ((,) <$> position <* symbolic '(' <*> varPattern ename) <* colon <*> type' <* symbolic ')'
  bindVarPattern i $ \ v -> mk start (v S.::: t) <$ arrow <*> self <*> position
  where
  mk start t b end = setSpan (Span start end) $ review D.bind_ (t, b)


-- Types

typeTable :: (Monad p, PositionParsing p) => Table (Facet p) T.Type
typeTable = [ Op.Operator (forAll (curry (review T.forAll_))) ] : monotypeTable

monotypeTable :: (Monad p, PositionParsing p) => Table (Facet p) T.Type
monotypeTable =
  [ [ Infix R (pack "->") (\ s -> fmap (setSpan s) . curry (review T.arrow_)) ]
  , [ Infix L mempty (\ s -> fmap (setSpan s) . curry (review T.app_)) ]
  , [ -- FIXME: we should treat these as globals.
      Atom (T._Type <$ token (string "Type"))
    , Atom (T._Void <$ token (string "Void"))
    , Atom (T._Unit <$ token (string "Unit"))
    , Atom tvar
    ]
  ]

forAll
  :: (Monad p, PositionParsing p, Spanned res)
  => ((N.UName S.::: T.Type) -> res -> res)
  -> OperatorParser (Facet p) res
forAll mk self _ = do
  start <- position
  (names, ty) <- braces ((,) <$> commaSep1 tname <* colon <*> type')
  arrow *> foldr (loop start ty) self names
  where
  loop start ty i rest = bind i $ \ v -> mk' start (v S.::: ty) <$> rest <*> position
  mk' start t b end = setSpan (Span start end) $ mk t b

type' :: (Monad p, PositionParsing p) => Facet p T.Type
type' = build typeTable (terminate parens (parseOperator (Infix L (pack ",") (\ s -> fmap (setSpan s) . curry (review T.prd_)))))

monotype :: (Monad p, PositionParsing p) => Facet p T.Type
monotype = build monotypeTable (terminate parens (parseOperator (Infix L (pack ",") (\ s -> fmap (setSpan s) . curry (review T.prd_)))))

tvar :: (Monad p, PositionParsing p) => Facet p T.Type
tvar = token (settingSpan (runUnspaced (fmap (either (review T.global_ . N.T) (review T.bound_)) . resolve <$> tname <*> Unspaced env <?> "variable")))


-- Expressions

exprTable :: (Monad p, PositionParsing p) => Table (Facet p) E.Expr
exprTable =
  [ [ Infix L mempty (\ s -> fmap (setSpan s) . curry (review E.app_)) ]
  , [ Atom comp
    , Atom (review E.hole_ <$> hname)
    , Atom evar
    ]
  ]

expr :: (Monad p, PositionParsing p) => Facet p E.Expr
expr = build exprTable (terminate parens (parseOperator (Infix L (pack ",") (\ s -> fmap (setSpan s) . curry (review E.prd_)))))

comp :: (Monad p, PositionParsing p) => Facet p E.Expr
comp = settingSpan (braces (review E.comp_ <$> clauses))
  where
  clauses
    =   sepBy1 clause comma
    <|> pure <$> body
    <|> pure []

clause :: (Monad p, PositionParsing p) => Facet p (C.Clause E.Expr)
clause = (try (some ((,) <$> position <*> pattern) <* arrow) >>= foldr go body) <?> "clause"
  where
  go (start, p) rest = bindPattern p $ \ p' -> do
    c <- review C.clause_ . (,) p' <$> rest
    end <- position
    pure $ setSpan (Span start end) c

body :: (Monad p, PositionParsing p) => Facet p (C.Clause E.Expr)
body = review C.body_ <$> expr

evar :: (Monad p, PositionParsing p) => Facet p E.Expr
evar
  =   token (settingSpan (runUnspaced (fmap (either (review E.global_ . N.E) (review E.bound_)) . resolve <$> ename <*> Unspaced env <?> "variable")))
  <|> try (token (settingSpan (runUnspaced (review E.global_ . N.O <$> Unspaced (parens oname))))) -- FIXME: would be better to commit once we see a placeholder, but try doesn’t really let us express that


-- Patterns

bindPattern :: PositionParsing p => P.Pattern N.EName -> (P.Pattern N.UName -> Facet p a) -> Facet p a
bindPattern p f = case P.out p of
  P.Wildcard -> bind (N.EName N.__) (const (f (review P.wildcard_ (P.ann p))))
  P.Var n    -> bind n              (f . review P.var_ . (,) (P.ann p))
  P.Tuple ps -> foldr (\ p k ps -> bindPattern p $ \ p' -> k (ps . (p':))) (f . review P.tuple_ . (,) (P.ann p) . ($ [])) ps id

bindVarPattern :: Maybe N.EName -> (N.UName -> Facet p res) -> Facet p res
bindVarPattern Nothing  = bind (N.EName N.__)
bindVarPattern (Just n) = bind n


varPattern :: (Monad p, TokenParsing p) => p name -> p (Maybe name)
varPattern n = Just <$> n <|> Nothing <$ wildcard


wildcard :: (Monad p, TokenParsing p) => p ()
wildcard = reserve enameStyle "_"

-- FIXME: patterns
pattern :: (Monad p, PositionParsing p) => p (P.Pattern N.EName)
pattern
  =   review P.var_ <$> spanned ename
  <|> review P.wildcard_ <$> spanning wildcard
  <|> review P.tuple_ <$> spanned (parens (commaSep pattern))
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

tname :: (Monad p, TokenParsing p) => p N.TName
tname = ident tnameStyle

dname :: (Monad p, TokenParsing p) => p N.DName
dname  = N.E <$> ename <|> N.T <$> tname <|> N.O <$> oname

mname :: (Monad p, TokenParsing p) => p N.MName
mname = token (runUnspaced (foldl' (N.:.) . N.MName <$> comp <* dot <*> sepBy comp dot))
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
