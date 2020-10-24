module Facet.Parser
( runFacet
, Facet(..)
, module'
, module''
, moduleHeader
, decl
, type'
, expr
, whole
, mname
) where

import           Control.Algebra ((:+:))
import           Control.Applicative (Alternative(..))
import           Control.Carrier.Reader
import           Control.Carrier.State.Strict
import           Control.Monad.Trans.Class
import           Data.Bool (bool)
import           Data.Char (isSpace)
import qualified Data.CharSet as CharSet
import qualified Data.CharSet.Unicode as Unicode
import           Data.Coerce (Coercible, coerce)
import           Data.Foldable (foldl')
import qualified Data.HashSet as HashSet
import           Data.List (elemIndex, uncons)
import qualified Data.List.NonEmpty as NE
import           Data.Text (pack)
import           Facet.Effect.Parser
import qualified Facet.Name as N
import           Facet.Parser.Table as Op
import           Facet.Span
import           Facet.Stack
import qualified Facet.Surface as S
import           Facet.Syntax
import           Prelude hiding (lines, null, product, span)
import           Text.Parser.Char
import           Text.Parser.Combinators
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
-- resolve module-local definitions in the parser
-- resolve imported definitions in the parser

runFacet :: Functor m => [N.UName] -> [AnyOperator] -> Facet m a -> m a
runFacet env ops (Facet m) = evalState ops (m env)

bind :: Coercible t N.UName => t -> (N.UName -> Facet m a) -> Facet m a
bind n b = Facet $ \ env -> StateC $ \ ops -> let { n' = coerce n ; Facet run = b n' } in runState ops (run (n':env))

resolve :: Coercible t N.UName => t -> [N.UName] -> Either t N.Index
resolve n = maybe (Left n) (Right . N.Index) . elemIndex @N.UName (coerce n)

env :: Monad m => Facet m [N.UName]
env = Facet pure

newtype AnyOperator = AnyOperator { runAnyOperator :: forall sig p . (Has Parser sig p, TokenParsing p) => Operator p (S.Ann S.Expr) }

newtype Facet m a = Facet ([N.UName] -> StateC [AnyOperator] m a)
  deriving (Algebra (Reader [N.UName] :+: State [AnyOperator] :+: sig), Alternative, Applicative, Functor, Monad, MonadFail) via ReaderC [N.UName] (StateC [AnyOperator] m)

instance (Monad p, Parsing p) => Parsing (Facet p) where
  try (Facet m) = Facet $ \ env -> StateC $ \ s -> try (runState s (m env))
  Facet m <?> l = Facet $ \ env -> StateC $ \ s -> runState s (m env) <?> l
  unexpected = lift . unexpected
  eof = lift eof
  notFollowedBy (Facet m) = Facet $ \ env -> StateC $ \ s -> (s,) <$> notFollowedBy (evalState s (m env))

instance (Monad p, CharParsing p) => CharParsing (Facet p) where
  satisfy = lift . satisfy
  char    = lift . char
  notChar = lift . notChar
  anyChar = lift anyChar
  string  = lift . string
  text    = lift . text

instance (Monad m, TokenParsing m) => TokenParsing (Facet m) where
  someSpace = buildSomeSpaceParser (skipSome (satisfy isSpace)) emptyCommentStyle{ _commentLine = "#" }

instance MonadTrans Facet where
  lift = Facet . const . lift


whole :: TokenParsing p => p a -> p a
whole p = whiteSpace *> p <* eof


-- Modules

-- FIXME: preserve comments, presumably in 'S.Ann'
module' :: (Has Parser sig p, TokenParsing p) => Facet p (S.Ann S.Module)
module' = anned $ do
  (name, imports) <- moduleHeader
  S.Module name imports <$> many decl

-- | Parse a module, using the provided callback to give the parser feedback on imports.
module'' :: (Has Parser sig p, TokenParsing p) => (S.Ann S.Import -> Facet p ()) -> Facet p (S.Ann S.Module)
module'' onImport = anned (S.Module <$> mname <* colon <* symbol "Module" <*> option [] (brackets (commaSep import'')) <*> many decl)
  where
  import'' = do
    i <- import'
    onImport i
    pure i

moduleHeader :: (Has Parser sig p, TokenParsing p) => Facet p (N.MName, [S.Ann S.Import])
moduleHeader = (,) <$> mname <* colon <* symbol "Module" <*> option [] (brackets (commaSep import'))


-- Declarations

import' :: (Has Parser sig p, TokenParsing p) => Facet p (S.Ann S.Import)
import' = anned $ S.Import <$> mname

decl :: (Has Parser sig p, TokenParsing p) => Facet p (S.Ann (N.DName, S.Ann S.Decl))
decl = choice
  [ termDecl
  , dataDecl
  ]
  where

termDecl :: (Has Parser sig p, TokenParsing p) => Facet p (S.Ann (N.DName, S.Ann S.Decl))
termDecl = anned $ do
  name <- dename
  case name of
    N.O op -> do
      op' <- case op of
        N.Prefix  l  -> pure $ AnyOperator $ Prefix l (unary name)
        N.Postfix r  -> pure $ AnyOperator $ Postfix r (unary name)
        N.Infix   m  -> do
          assoc <- brackets $ choice
            [ N.N <$ symbol "non-assoc"
            , N.L <$ symbol "left-assoc"
            , N.R <$ symbol "right-assoc"
            , N.A <$ symbol "assoc"
            ]
          pure $ AnyOperator $ Infix assoc m (binary name)
        N.Outfix l r -> pure $ AnyOperator $ Outfix l r (unary name)
      -- FIXME: record the operator name and associativity in the module.
      modify (op' :)
    _      -> pure ()
  decl <- colon *> anned (S.TDecl <$> typeSig S.TDForAll ename (S.TDBody <$> monotype <*> comp))
  pure (name, decl)
  where
  binary name e1@(S.Ann s _) e2 = S.Ann s (S.free name) S.$$ e1 S.$$ e2
  unary name e@(S.Ann s _) = S.Ann s (S.free name) S.$$ e

-- FIXME: how do we distinguish between data and interface declarations?
dataDecl :: (Has Parser sig p, TokenParsing p) => Facet p (S.Ann (N.DName, S.Ann S.Decl))
dataDecl = anned $ (,) <$> dtname <* colon <*> anned (S.DDecl <$> typeSig S.DDForAll tname (S.DDBody <$> monotype <*> braces (commaSep con)))


typeSig
  :: (Has Parser sig p, TokenParsing p)
  => (Pl_ N.UName ::: S.Ann S.Expr -> S.Ann res -> res)
  -> Facet p N.UName
  -> Facet p res
  -> Facet p (S.Ann res)
typeSig (-->) name body = go
  where
  go = choice [ forAll (-->) go, binder (-->) name go, anned body ]

binder
  :: (Has Parser sig p, TokenParsing p)
  => (Pl_ N.UName ::: S.Ann S.Expr -> S.Ann res -> res)
  -> Facet p N.UName
  -> Facet p (S.Ann res)
  -> Facet p (S.Ann res)
binder (-->) name k = do
  -- FIXME: signatures
  ((start, i), t) <- nesting $ (,) <$> try ((,) <$> position <* lparen <*> (coerce <$> name <|> N.__ <$ wildcard) <* colon) <*> type' <* rparen
  bind i $ \ v -> mk start (ex v ::: t) <$ arrow <*> k <*> position
  where
  mk start t b end = S.Ann (Span start end) (t --> b)

con :: (Has Parser sig p, TokenParsing p) => Facet p (S.Ann (N.UName ::: S.Ann S.Expr))
con = anned ((:::) <$> cname <* colon <*> type')


-- Types

monotypeTable :: (Has Parser sig p, TokenParsing p) => Table (Facet p) (S.Ann S.Expr)
monotypeTable =
  [ [ Infix L mempty (S.$$) ]
  , [ -- FIXME: we should treat these as globals.
      Atom (anned (S.Type <$ token (string "Type")))
    , Atom (anned (S.Interface <$ token (string "Interface")))
      -- FIXME: holes in types
    , Atom tvar
    ]
  ]

forAll
  :: (Has Parser sig p, TokenParsing p)
  => (Pl_ N.UName ::: S.Ann S.Expr -> S.Ann res -> res)
  -> Facet p (S.Ann res) -> Facet p (S.Ann res)
forAll mk k = do
  start <- position
  -- FIXME: parse multiple sets of bindings within a single set of braces.
  (names, ty) <- braces ((,) <$> commaSep1 tname <* colon <*> type')
  arrow *> foldr (loop start ty) k names
  where
  loop start ty i rest = bind i $ \ v -> mk' start (im v ::: ty) <$> rest <*> position
  mk' start t b end = S.Ann (Span start end) (mk t b)

type' :: (Has Parser sig p, TokenParsing p) => Facet p (S.Ann S.Expr)
type' = forAll (\ (n ::: _T) b -> S.ForAll (S.Binding (Just (out n)) [] _T) b) type' <|> monotype

monotype :: (Has Parser sig p, TokenParsing p) => Facet p (S.Ann S.Expr)
monotype = fn mono
  where
  fn loop = do
    start <- position
    delta <- option [] sig
    a <- loop
    b <- optional (arrow *> fn loop)
    end <- position
    pure $ case b of
      Just b  -> S.Ann (Span start end) $ S.ForAll (S.Binding Nothing delta a) b
      -- FIXME: preserve the signature on the return type.
      Nothing -> a
  -- FIXME: support type operators
  mono = build monotypeTable (parens . fn)

tvar :: (Has Parser sig p, TokenParsing p) => Facet p (S.Ann S.Expr)
tvar = choice
  [ token (anned (runUnspaced (fmap (either (S.free . N.T) S.bound) . resolve <$> tname <*> Unspaced env <?> "variable")))
  , fmap S.qual <$> qname
  ]


-- Signatures

-- can appear:
-- - before an argument type
-- - before a return type

sig :: (Has Parser sig p, TokenParsing p) => Facet p [S.Ann S.Delta]
sig = brackets (commaSep delta) <?> "signature"
  where
  var
    =   token (anned (runUnspaced (fmap (either (S.Free Nothing . N.T) S.Bound) . resolve <$> tname <*> Unspaced env)))
    <|> fmap (\ (m N.:.: n) -> S.Free (Just m) n) <$> qname
    <?> "variable"
  delta = anned $ S.Delta <$> head <*> (fromList <$> many var)
  head = fmap mkHead <$> token (anned (runUnspaced (sepByNonEmpty comp dot)))
  mkHead cs = (uncurry (foldl' (N.:.) . N.MName) <$> uncons (NE.init cs), N.T (N.UName (NE.last cs)))
  comp = ident tnameStyle


-- Expressions

exprTable :: (Has Parser sig p, TokenParsing p) => Table (Facet p) (S.Ann S.Expr)
exprTable =
  [ [ Infix L mempty (S.$$) ]
  -- FIXME: model this as application to unit instead
  -- FIXME: can we parse () as a library-definable symbol? nullfix, maybe?
  , [ Postfix (pack "!") id ]
  , [ Atom comp
    , Atom hole
    , Atom evar
    ]
  ]

expr :: (Has Parser sig p, TokenParsing p) => Facet p (S.Ann S.Expr)
expr = do
  ops <- get
  build (map runAnyOperator ops:exprTable) parens

comp :: (Has Parser sig p, TokenParsing p) => Facet p (S.Ann S.Expr)
-- NB: We parse sepBy1 and the empty case separately so that it doesn’t succeed at matching 0 clauses and then expect a closing brace when it sees a nullary computation
comp = anned (S.Comp <$> anned (braces (S.Clauses <$> sepBy1 clause comma <|> S.Expr <$> expr <|> pure (S.Clauses []))))

clause :: (Has Parser sig p, TokenParsing p) => Facet p (NE.NonEmpty (S.Ann S.Pattern), S.Ann S.Expr)
clause = (do
  ps <- try (NE.some1 pattern <* arrow)
  b' <- foldr (bindPattern . S.out) expr ps
  pure (ps, b')) <?> "clause"

evar :: (Has Parser sig p, TokenParsing p) => Facet p (S.Ann S.Expr)
evar = choice
  [ token (anned (runUnspaced (fmap (either (S.free . N.E) S.bound) . resolve <$> ename <*> Unspaced env <?> "variable")))
    -- FIXME: would be better to commit once we see a placeholder, but try doesn’t really let us express that
  , try (token (anned (runUnspaced (S.free . N.O <$> Unspaced (parens oname)))))
  , fmap S.qual <$> qname
  ]

hole :: (Has Parser sig p, TokenParsing p) => p (S.Ann S.Expr)
hole = token (anned (runUnspaced (S.Hole <$> ident hnameStyle)))
  where
  hnameStyle = IdentifierStyle "hole name" (char '?') nameChar reserved Identifier ReservedIdentifier


-- Patterns

bindPattern :: Has Parser sig p => S.Pattern -> Facet p a -> Facet p a
bindPattern p m = case p of
  S.PVar n      -> bind n (const m)
  S.PCon _ ps   -> foldr (bindPattern . S.out) m ps
  S.PEff _ ps k -> foldr (bindPattern . S.out) (bind k (const m)) ps


wildcard :: (Monad p, TokenParsing p) => p ()
wildcard = reserve enameStyle "_"

pattern :: (Has Parser sig p, TokenParsing p) => p (S.Ann S.Pattern)
pattern = choice
  [ anned (S.PVar      <$> ename)
  , anned (S.PVar N.__ <$  wildcard)
  , try (parens (anned (S.PCon <$> cname <*> (fromList <$> many pattern))))
  , brackets (anned (S.PEff <$> ename <*> (fromList <$> many pattern) <* symbolic ';' <*> (ename <|> N.__ <$ wildcard)))
  ] <?> "pattern"


-- Names

ename :: (Monad p, TokenParsing p) => p N.UName
ename  = ident enameStyle

oname :: (Monad p, TokenParsing p) => p N.Op
oname = choice
  [ postOrIn <$ place <*> comp <*> option False (True <$ place)
  , try (outOrPre <$> comp <* place) <*> optional comp
  ]
  where
  place = wildcard
  comp = ident onameStyle
  outOrPre s e = maybe (N.Prefix s) (N.Outfix s) e
  postOrIn c = bool (N.Postfix c) (N.Infix c)

_onameN :: (Monad p, TokenParsing p) => p N.OpN
_onameN = choice
  [ postOrIn <$ place <*> sepByNonEmpty comp place <*> option False (True <$ place)
  , try (uncurry . outOrPre <$> comp <* place) <*> ((,) <$> sepBy1 comp place <*> option False (True <$ place) <|> pure ([], True))
  ]
  where
  place = wildcard
  comp = ident onameStyle
  outOrPre c cs = bool (N.OutfixN c (init cs) (last cs)) (N.PrefixN c cs)
  postOrIn cs = bool (N.PostfixN (NE.init cs) (NE.last cs)) (N.InfixN cs)

cname, tname :: (Monad p, TokenParsing p) => p N.UName
cname = ident cnameStyle
tname = ident tnameStyle

dename, dtname :: (Monad p, TokenParsing p) => p N.DName
dename  = N.E <$> ename <|> N.O <$> oname
dtname  = N.T <$> tname

mname :: (Monad p, TokenParsing p) => p N.MName
mname = token (runUnspaced (foldl' (N.:.) . N.MName <$> comp <* dot <*> sepBy comp dot))
  where
  comp = ident tnameStyle

qname :: (Has Parser sig p, TokenParsing p) => p (S.Ann N.QName)
qname = token (anned (runUnspaced (fmap (N.:.:) . foldl' (N.:.) . N.MName <$> comp <* dot <*> many (comp <* dot) <*> (dename <|> dtname))))
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


arrow :: TokenParsing p => p String
arrow = symbol "->"

lparen :: TokenParsing p => p Char
lparen = symbolic '('

rparen :: TokenParsing p => p Char
rparen = symbolic ')'


anned :: Has Parser sig p => p a -> p (S.Ann a)
anned p = mk <$> position <*> p <*> position
  where
  mk s a e = (S.Ann (Span s e) a)
