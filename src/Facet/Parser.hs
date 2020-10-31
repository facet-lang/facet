{-# LANGUAGE UndecidableInstances #-}
module Facet.Parser
( whole
, makeOperator
, module'
, moduleHeader
, decl
, type'
, expr
, mname
, runFacet
, Facet(..)
) where

import           Control.Algebra ((:+:))
import           Control.Applicative (Alternative(..))
import           Control.Carrier.Reader
import qualified Control.Carrier.State.Strict as C
import qualified Control.Carrier.Writer.Strict as C
import           Control.Effect.State
import           Control.Effect.Writer
import           Control.Monad.Fix
import           Control.Monad.Trans.Class
import           Data.Bool (bool)
import           Data.Char (isSpace)
import qualified Data.CharSet as CharSet
import qualified Data.CharSet.Unicode as Unicode
import           Data.Foldable (foldl')
import           Data.Functor (void)
import qualified Data.HashSet as HashSet
import           Data.List (uncons)
import qualified Data.List.NonEmpty as NE
import           Data.Text (pack)
import           Data.Void
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

-- TODO:
-- list literals
-- string literals
-- numeric literals
-- forcing nullary computations
-- resolve module-local definitions in the parser
-- resolve imported definitions in the parser

-- FIXME: allow operators to be introduced and scoped locally

whole :: TokenParsing p => p a -> p a
whole p = whiteSpace *> p <* eof


makeOperator :: (N.Op, N.Assoc) -> Operator (S.Ann (S.Expr Void))
makeOperator (op, assoc) = (op, assoc, nary (N.O op))
  where
  nary name es = foldl' (S.annBinary S.App) (S.Ann (S.ann (head es)) Nil (S.free name)) es


-- Modules

-- FIXME: preserve comments, presumably in 'S.Ann'
module' :: (Has Parser sig p, Has (State [Operator (S.Ann (S.Expr Void))]) sig p, Has (Writer (Stack (Span, S.Comment))) sig p, TokenParsing p) => p (S.Ann (S.Module Void))
module' = anned $ do
  (name, imports) <- moduleHeader
  decls <- many decl
  ops <- get @[Operator (S.Ann (S.Expr Void))]
  pure $ S.Module name imports (map (\ (op, assoc, _) -> (op, assoc)) ops) decls

-- FIXME: pick a better syntax for imports, something we can use in the REPL.
moduleHeader :: (Has Parser sig p, Has (Writer (Stack (Span, S.Comment))) sig p, TokenParsing p) => p (N.MName, [S.Ann S.Import])
moduleHeader = (,) <$ reserve dnameStyle "module" <*> mname <* colon <* symbol "Module" <*> option [] (braces (commaSep import'))


-- Declarations

import' :: (Has Parser sig p, Has (Writer (Stack (Span, S.Comment))) sig p, TokenParsing p) => p (S.Ann S.Import)
import' = anned $ S.Import <$ reserve dnameStyle "import" <*> mname

decl :: (Has Parser sig p, Has (State [Operator (S.Ann (S.Expr Void))]) sig p, Has (Writer (Stack (Span, S.Comment))) sig p, TokenParsing p) => p (S.Ann (N.DName, S.Ann (S.Decl Void)))
decl = choice
  [ termDecl
  , dataDecl
  , interfaceDecl
  ]

-- FIXME: operators aren’t available until after their declarations have been parsed.
-- FIXME: parse operator declarations in datatypes.
-- FIXME: parse operator declarations in interfaces.
termDecl :: (Has Parser sig p, Has (State [Operator (S.Ann (S.Expr Void))]) sig p, Has (Writer (Stack (Span, S.Comment))) sig p, TokenParsing p) => p (S.Ann (N.DName, S.Ann (S.Decl Void)))
termDecl = anned $ do
  name <- dename
  case name of
    N.O op -> do
      assoc <- case op of
        N.Infix _ -> option N.N $ brackets $ choice
          [ N.N <$ symbol "non-assoc"
          , N.L <$ symbol "left-assoc"
          , N.R <$ symbol "right-assoc"
          , N.A <$ symbol "assoc"
          ]
        _ -> pure N.N
      modify (makeOperator (op, assoc) :)
    _      -> pure ()
  decl <- anned $ S.Decl <$ colon <*> typeSig (choice [ imBinding, exBinding ename ]) type' <*> (S.TermDef <$> comp)
  pure (name, decl)

dataDecl :: (Has Parser sig p, Has (Writer (Stack (Span, S.Comment))) sig p, TokenParsing p) => p (S.Ann (N.DName, S.Ann (S.Decl Void)))
dataDecl = anned $ (,) <$ reserve dnameStyle "data" <*> dtname <* colon <*> anned (S.Decl <$> typeSig (choice [ imBinding, exBinding tname ]) type' <*> (S.DataDef <$> braces (commaSep con)))

interfaceDecl :: (Has Parser sig p, Has (Writer (Stack (Span, S.Comment))) sig p, TokenParsing p) => p (S.Ann (N.DName, S.Ann (S.Decl Void)))
interfaceDecl = anned $ (,) <$ reserve dnameStyle "interface" <*> dtname <* colon <*> anned (S.Decl <$> typeSig (choice [ imBinding, exBinding tname ]) type' <*> (S.InterfaceDef <$> braces (commaSep con)))

con :: (Has Parser sig p, Has (Writer (Stack (Span, S.Comment))) sig p, TokenParsing p) => p (S.Ann (N.UName ::: S.Ann (S.Comp Void)))
con = anned ((:::) <$> cname <* colon <*> tcomp)


typeSig
  :: (Has Parser sig p, Has (Writer (Stack (Span, S.Comment))) sig p, TokenParsing p)
  => p (S.Ann (S.Binding Void))
  -> p (S.Ann (S.Expr Void))
  -> p (S.Ann (S.Comp Void))
typeSig binding body = anned $ do
  bindings <- many (try (binding <* arrow))
  S.Comp bindings <$> option [] sig <*> body

exBinding :: (Has Parser sig p, Has (Writer (Stack (Span, S.Comment))) sig p, TokenParsing p) => p N.UName -> p (S.Ann (S.Binding Void))
exBinding name = anned $ nesting $ try (S.Binding Ex . pure <$ lparen <*> (name <|> N.__ <$ wildcard) <* colon) <*> option [] sig <*> type' <* rparen

imBinding :: (Has Parser sig p, Has (Writer (Stack (Span, S.Comment))) sig p, TokenParsing p) => p (S.Ann (S.Binding Void))
imBinding = anned $ braces $ S.Binding Im . NE.fromList <$> commaSep1 tname <* colon <*> option [] sig <*> type'

nonBinding :: (Has Parser sig p, Has (Writer (Stack (Span, S.Comment))) sig p, TokenParsing p) => p (S.Ann (S.Binding Void))
nonBinding = anned $ S.Binding Ex (pure N.__) <$> option [] sig <*> tatom


-- Types

-- FIXME: kind ascriptions
monotypeTable :: (Has Parser sig p, Has (Writer (Stack (Span, S.Comment))) sig p, TokenParsing p) => Table p (S.Ann (S.Type Void))
monotypeTable =
  [ [ parseOperator (N.Infix mempty, N.L, foldl1 (S.annBinary S.App)) ]
  , [ -- FIXME: we should treat these as globals.
      atom (anned (S.Type <$ token (string "Type")))
    , atom (anned (S.TInterface <$ token (string "Interface")))
    , atom (anned (S.TString    <$ token (string "String")))
      -- FIXME: holes in types
    , atom tvar
    ]
  ]


type' :: (Has Parser sig p, Has (Writer (Stack (Span, S.Comment))) sig p, TokenParsing p) => p (S.Ann (S.Type Void))
type' = anned $ S.TComp <$> tcomp

tcomp :: (Has Parser sig p, Has (Writer (Stack (Span, S.Comment))) sig p, TokenParsing p) => p (S.Ann (S.Comp Void))
tcomp = typeSig (choice [ imBinding, nonBinding ]) tatom

-- FIXME: support type operators
tatom :: (Has Parser sig p, Has (Writer (Stack (Span, S.Comment))) sig p, TokenParsing p) => p (S.Ann (S.Type Void))
tatom = build monotypeTable $ parens type'

tvar :: (Has Parser sig p, Has (Writer (Stack (Span, S.Comment))) sig p, TokenParsing p) => p (S.Ann (S.Expr Void))
tvar = choice
  [ token (anned (runUnspaced (S.free . N.T <$> tname  <?> "variable")))
  , fmap S.qual <$> qname
  ]


-- Signatures

-- can appear:
-- - before an argument type
-- - before a return type

sig :: (Has Parser sig p, Has (Writer (Stack (Span, S.Comment))) sig p, TokenParsing p) => p [S.Ann (S.Interface Void)]
sig = brackets (commaSep delta) <?> "signature"
  where
  delta = anned $ S.Interface <$> head <*> (fromList <$> many type')
  head = fmap mkHead <$> token (anned (runUnspaced (sepByNonEmpty comp dot)))
  mkHead cs = (uncurry (foldl' (N.:.) . N.MName) <$> uncons (NE.init cs), N.T (N.UName (NE.last cs)))
  comp = ident tnameStyle


-- Expressions

exprTable :: (Has Parser sig p, Has (State [Operator (S.Ann (S.Expr Void))]) sig p, Has (Writer (Stack (Span, S.Comment))) sig p, TokenParsing p) => Table p (S.Ann (S.Expr Void))
exprTable =
  [ [ parseOperator (N.Infix (pack ":"), N.R, foldr1 (S.annBinary S.As)) ]
  , [ parseOperator (N.Infix mempty, N.L, foldl1 (S.annBinary S.App)) ]
  -- FIXME: model this as application to unit instead
  -- FIXME: can we parse () as a library-definable symbol? nullfix, maybe?
  , [ parseOperator (N.Postfix (pack "!"), N.L, S.annUnary S.Force . head) ]
  , [ atom comp, atom hole, atom evar, atom (token (anned (runUnspaced (S.String <$> stringLiteral)))) ]
  ]

expr :: (Has Parser sig p, Has (State [Operator (S.Ann (S.Expr Void))]) sig p, Has (Writer (Stack (Span, S.Comment))) sig p, TokenParsing p) => p (S.Ann (S.Expr Void))
expr = do
  ops <- get
  let rec = build (map parseOperator ops:exprTable) $ parens rec
  rec

comp :: (Has Parser sig p, Has (State [Operator (S.Ann (S.Expr Void))]) sig p, Has (Writer (Stack (Span, S.Comment))) sig p, TokenParsing p) => p (S.Ann (S.Expr Void))
-- NB: We parse sepBy1 and the empty case separately so that it doesn’t succeed at matching 0 clauses and then expect a closing brace when it sees a nullary computation
comp = anned (braces (S.Lam <$> sepBy1 clause comma <|> S.Thunk <$> expr <|> pure (S.Lam [])))

clause :: (Has Parser sig p, Has (State [Operator (S.Ann (S.Expr Void))]) sig p, Has (Writer (Stack (Span, S.Comment))) sig p, TokenParsing p) => p (S.Clause Void)
clause = S.Clause <$> try (patternP <* arrow) <*> expr <?> "clause"

evar :: (Has Parser sig p, Has (Writer (Stack (Span, S.Comment))) sig p, TokenParsing p) => p (S.Ann (S.Expr Void))
evar = choice
  [ token (anned (runUnspaced (S.free . N.E <$> ename <?> "variable")))
    -- FIXME: would be better to commit once we see a placeholder, but try doesn’t really let us express that
  , try (token (anned (runUnspaced (S.free . N.O <$> Unspaced (parens oname)))))
  , fmap S.qual <$> qname
  ]

hole :: (Has Parser sig p, Has (Writer (Stack (Span, S.Comment))) sig p, TokenParsing p) => p (S.Ann (S.Expr Void))
hole = token (anned (runUnspaced (S.Hole <$> ident hnameStyle)))
  where
  hnameStyle = IdentifierStyle "hole name" (char '?') nameChar reserved Identifier ReservedIdentifier


-- Patterns

wildcard :: (Monad p, TokenParsing p) => p ()
wildcard = reserve enameStyle "_"

patternP :: (Has Parser sig p, Has (Writer (Stack (Span, S.Comment))) sig p, TokenParsing p) => p (S.Ann (S.Pattern Void))
patternP = choice
  [ anned (S.PVar      <$> ename)
  , anned (S.PWildcard <$  wildcard)
  , try (parens (anned (S.PCon <$> cname <*> many patternP)))
  , brackets (anned (S.PEff <$> ename <*> many patternP <* symbolic ';' <*> (ename <|> N.__ <$ wildcard)))
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
dename  = N.E <$> ident dnameStyle <|> N.O <$> oname
dtname  = N.T <$> tname

mname :: (Monad p, TokenParsing p) => p N.MName
mname = token (runUnspaced (foldl' (N.:.) . N.MName <$> comp <* dot <*> sepBy comp dot))
  where
  comp = ident tnameStyle

qname :: (Has Parser sig p, Has (Writer (Stack (Span, S.Comment))) sig p, TokenParsing p) => p (S.Ann N.QName)
qname = token (anned (runUnspaced (fmap (N.:.:) . foldl' (N.:.) . N.MName <$> comp <* dot <*> many (comp <* dot) <*> (dename <|> dtname))))
  where
  comp = ident tnameStyle


reserved :: HashSet.HashSet String
reserved = HashSet.singleton "_"

declarationReserved :: HashSet.HashSet String
declarationReserved = HashSet.fromList ["_", "data", "import", "interface", "module"]

nameChar :: CharParsing p => p Char
nameChar = alphaNum <|> char '_'

opChar :: CharParsing p => p Char
opChar = oneOfSet (CharSet.difference (Unicode.punctuation <> Unicode.symbol) (CharSet.fromList "(){}"))

dnameStyle :: CharParsing p => IdentifierStyle p
dnameStyle = IdentifierStyle "declaration name" (lower <|> char '_') nameChar declarationReserved Identifier ReservedIdentifier

enameStyle :: CharParsing p => IdentifierStyle p
enameStyle = IdentifierStyle "name" (lower <|> char '_') nameChar reserved Identifier ReservedIdentifier

onameStyle :: CharParsing p => IdentifierStyle p
onameStyle = IdentifierStyle "operator" opChar opChar mempty Highlight.Operator ReservedOperator

cnameStyle :: CharParsing p => IdentifierStyle p
cnameStyle = IdentifierStyle "constructor name" lower nameChar reserved Constructor ReservedConstructor

tnameStyle :: CharParsing p => IdentifierStyle p
tnameStyle = IdentifierStyle "type name" upper nameChar reserved Identifier ReservedIdentifier


arrow :: TokenParsing p => p String
arrow = symbol "->"

lparen :: TokenParsing p => p Char
lparen = symbolic '('

rparen :: TokenParsing p => p Char
rparen = symbolic ')'


anned :: (Has Parser sig p, Has (Writer (Stack (Span, S.Comment))) sig p) => p a -> p (S.Ann a)
anned p = mk <$> censor @(Stack (Span, S.Comment)) (const Nil) (listen @(Stack (Span, S.Comment)) ((,,) <$> position <*> p <*> position))
  where
  mk (cs, (s, a, e)) = S.Ann (Span s e) cs a


-- Parsing carriers

runFacet :: Functor m => [Operator (S.Ann (S.Expr Void))] -> Facet m a -> m a
runFacet ops (Facet m) = snd <$> C.runWriter (runWriterC (C.evalState ops (runStateC m)))

newtype Facet m a = Facet (StateC [Operator (S.Ann (S.Expr Void))] (WriterC (Stack (Span, S.Comment)) m) a)
  deriving (Algebra (State [Operator (S.Ann (S.Expr Void))] :+: Writer (Stack (Span, S.Comment)) :+: sig), Alternative, Applicative, Functor, Monad, MonadFail, MonadFix)

instance (Monad p, Parsing p) => Parsing (Facet p) where
  try (Facet m) = Facet $ try m
  Facet m <?> l = Facet $ m <?> l
  unexpected = lift . unexpected
  eof = lift eof
  notFollowedBy (Facet m) = Facet $ notFollowedBy m

instance (Monad p, CharParsing p) => CharParsing (Facet p) where
  satisfy = lift . satisfy
  char    = lift . char
  notChar = lift . notChar
  anyChar = lift anyChar
  string  = lift . string
  text    = lift . text

instance (Has Parser sig p, TokenParsing p) => TokenParsing (Facet p) where
  someSpace = skipSome (void (satisfy isSpace) <|> lineComment)
    where
    lineComment = (do
      start <- position
      void $ char '#'
      comment <- many (satisfy (/= '\n'))
      end <- position
      tell (Nil :> (Span start end, S.Comment (pack comment)))) <?> "line comment"

instance MonadTrans Facet where
  lift = Facet . lift . lift


newtype StateC s m a = StateC { runStateC :: C.StateC s m a }
  deriving (Algebra (State s :+: sig), Alternative, Applicative, Functor, Monad, MonadFail, MonadFix, MonadTrans)

instance (Monad p, Parsing p) => Parsing (StateC s p) where
  try (StateC m) = StateC $ C.StateC $ \ s -> try (C.runState s m)
  StateC m <?> l = StateC $ C.StateC $ \ s -> C.runState s m <?> l
  unexpected = lift . unexpected
  eof = lift eof
  notFollowedBy (StateC m) = StateC $ C.StateC $ \ s -> (s,) <$> notFollowedBy (C.evalState s m)


newtype WriterC w m a = WriterC { runWriterC :: C.WriterC w m a }
  deriving (Algebra (Writer w :+: sig), Alternative, Applicative, Functor, Monad, MonadFail, MonadFix, MonadTrans)

instance (Monad p, Parsing p) => Parsing (WriterC s p) where
  try (WriterC (C.WriterC m)) = WriterC $ C.WriterC $ C.StateC $ \ s -> try (C.runState s m)
  WriterC (C.WriterC m) <?> l = WriterC $ C.WriterC $ C.StateC $ \ s -> C.runState s m <?> l
  unexpected = lift . unexpected
  eof = lift eof
  notFollowedBy (WriterC (C.WriterC m)) = WriterC $ C.WriterC $ C.StateC $ \ s -> (s,) <$> notFollowedBy (C.evalState s m)
