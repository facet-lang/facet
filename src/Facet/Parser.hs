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
import           Data.Bool (bool)
import           Data.Char (isSpace)
import qualified Data.CharSet as CharSet
import qualified Data.CharSet.Unicode as Unicode
import           Data.Foldable (foldl')
import qualified Data.List.NonEmpty as NE
import qualified Data.HashSet as HashSet
import qualified Data.Map as Map
import           Data.Maybe (fromMaybe)
import           Data.Text (Text, pack)
import qualified Facet.Name as N
import           Facet.Parser.Table
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
import           Text.Parser.Token.Highlight
import           Text.Parser.Token.Style

-- case
-- : (x : a) -> (f : a -> b) -> b
-- { f x }

-- TODO:
-- list literals
-- numeric literals
-- forcing nullary computations

type EEnv = Map.Map N.EName E.Expr
type TEnv = Map.Map N.TName T.Type

runFacet :: EEnv -> TEnv -> Facet m a -> m a
runFacet e t (Facet m) = m e t

bindE :: N.EName -> (N.Name -> Facet m a) -> Facet m a
bindE n b = Facet $ \ e t -> let n' = N.Name (N.getEName n) (length e + length t) in runFacet (Map.insert n (review E.bound_ n') e) t (b n')

bindT :: N.TName -> (N.Name -> Facet m a) -> Facet m a
bindT n b = Facet $ \ e t -> let n' = N.Name (N.getTName n) (length e + length t) in runFacet e (Map.insert n (review T.bound_ n') t) (b n')

newtype Facet m a = Facet (EEnv -> TEnv -> m a)
  deriving (Alternative, Applicative, Functor, Monad, MonadFail) via ReaderC EEnv (ReaderC TEnv m)

eenv :: Applicative m => Facet m EEnv
eenv = Facet $ \ e _ -> pure e

tenv :: Applicative m => Facet m TEnv
tenv = Facet $ \ _ t -> pure t

instance Selective m => Selective (Facet m) where
  select f a = Facet $ \ e t -> select (runFacet e t f) (runFacet e t a)

instance Parsing p => Parsing (Facet p) where
  try (Facet m) = Facet $ \ e t -> try (m e t)
  Facet m <?> l = Facet $ \ e t -> m e t <?> l
  skipMany (Facet m) = Facet $ \ e t -> skipMany (m e t)
  unexpected = lift . unexpected
  eof = lift eof
  notFollowedBy (Facet m) = Facet $ \ e t -> notFollowedBy (m e t)

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
lift = Facet . const . const


whole :: TokenParsing p => p a -> p a
whole p = whiteSpace *> p <* eof


-- Modules

module' :: (Monad p, PositionParsing p) => Facet p M.Module
module' = spanning $ M.module' <$> mname <* colon <* symbol "Module" <*> braces (many decl)

decl :: (Monad p, PositionParsing p) => Facet p M.Module
decl = spanning $ M.def <$> dname <* colon <*> sig


-- Declarations

sigTable :: (Monad p, PositionParsing p) => Table (Facet p) D.Decl
sigTable =
  [ [ Binder (forAll (liftA2 (D.>=>))) ]
  , [ Binder binder ]
  ]

sig :: (Monad p, PositionParsing p) => Facet p D.Decl
sig = build sigTable (const ((D..=) <$> monotype <*> comp))

binder :: (Monad p, PositionParsing p) => OperatorParser (Facet p) D.Decl
binder self _ = spanning $ do
  (i, t) <- nesting $ (,) <$> try (symbolic '(' *> varPattern ename) <* colon <*> type' <* symbolic ')'
  bindVarPattern i $ \ v -> ((v S.::: t) D.>->) <$ arrow <*> self


-- Types

typeTable :: (Monad p, PositionParsing p) => Table (Facet p) T.Type
typeTable = [ Binder (forAll (liftA2 (curry (review T.forAll_)))) ] : monotypeTable

monotypeTable :: (Monad p, PositionParsing p) => Table (Facet p) T.Type
monotypeTable =
  [ [ Infix R (pack "->") (curry (review T.arrow_)) ]
  , [ Infix L mempty (curry (review T.app_)) ]
  , [ -- FIXME: we should treat Unit & Type as globals.
      Atom (T._Type <$ token (string "Type"))
    , Atom (T._Void <$ token (string "Void"))
    , Atom (T._Unit <$ token (string "Unit"))
    , Atom tvar
    ]
  ]

forAll
  :: (Spanned res, Monad p, PositionParsing p)
  => (Facet p (N.Name S.::: T.Type) -> Facet p res -> Facet p res)
  -> OperatorParser (Facet p) res
forAll (>=>) self _ = spanning $ do
  (names, ty) <- braces ((,) <$> commaSep1 tname <* colon <*> type')
  let loop i rest = bindT i $ \ v -> pure (v S.::: ty) >=> rest
  arrow *> foldr loop self names

type' :: (Monad p, PositionParsing p) => Facet p T.Type
type' = build typeTable (terminate parens (toBindParser (Infix L (pack ",") (curry (review T.prd_)))))

monotype :: (Monad p, PositionParsing p) => Facet p T.Type
monotype = build monotypeTable (terminate parens (toBindParser (Infix L (pack ",") (curry (review T.prd_)))))

tvar :: (Monad p, PositionParsing p) => Facet p T.Type
tvar = token (spanning (runUnspaced (resolve <$> tname <*> Unspaced tenv <?> "variable")))
  where
  resolve n env = fromMaybe (review T.global_ (N.T n)) (Map.lookup n env)


-- Expressions

exprTable :: (Monad p, PositionParsing p) => Table (Facet p) E.Expr
exprTable =
  [ [ Infix L mempty (curry (review E.app_)) ]
  , [ Atom comp
    , Atom (review E.hole_ <$> hname)
    , Atom evar
    ]
  ]

expr :: (Monad p, PositionParsing p) => Facet p E.Expr
expr = build exprTable (terminate parens (toBindParser (Infix L (pack ",") (curry (review E.prd_)))))

comp :: (Monad p, PositionParsing p) => Facet p E.Expr
comp = spanning (braces (review E.comp_ <$> clauses))
  where
  clauses
    =   sepBy1 clause comma
    <|> pure <$> body
    <|> pure []

clause :: (Monad p, PositionParsing p) => Facet p (C.Clause E.Expr)
clause = (do
  patterns <- try (some pattern <* arrow)
  bindPatterns patterns clause) <?> "clause"
  where
  clause vs = foldr (\ v -> fmap (review C.clause_ . (,) v)) body vs

body :: (Monad p, PositionParsing p) => Facet p (C.Clause E.Expr)
body = review C.body_ <$> expr

evar :: (Monad p, PositionParsing p) => Facet p E.Expr
evar
  =   token (spanning (runUnspaced (resolve <$> ename <*> Unspaced eenv <?> "variable")))
  <|> try (spanning (runUnspaced (review E.global_ . N.O <$> Unspaced (parens oname)))) -- FIXME: would be better to commit once we see a placeholder, but try doesn’t really let us express that
  where
  resolve n env = fromMaybe (review E.global_ (N.E n)) (Map.lookup n env)


-- Patterns

bindPatterns :: PositionParsing p => [P.Pattern N.EName] -> ([N.Name] -> Facet p a) -> Facet p a
bindPatterns ps f = foldr go f ps []
  where
  go p f vs = bindPattern p (f . (vs ++))

bindPattern :: PositionParsing p => P.Pattern N.EName -> ([N.Name] -> Facet p a) -> Facet p a
bindPattern p f = case P.out p of
  P.Wildcard -> bindE (N.EName N.__) (\ v -> f [v])
  P.Var n    -> bindE n              (\ v -> f [v])
  -- FIXME: this is incorrect since the structure doesn’t get used in the clause
  P.Tuple ps -> go [] ps
    where
    go vs []     = f vs
    go vs (p:ps) = bindPattern p $ \ vs' -> go (vs <> vs') ps
  P.Loc _ p  -> bindPattern p f

bindVarPattern :: Maybe N.EName -> (N.Name -> Facet p res) -> Facet p res
bindVarPattern Nothing  = bindE (N.EName N.__)
bindVarPattern (Just n) = bindE n


varPattern :: (Monad p, TokenParsing p) => p name -> p (Maybe name)
varPattern n = Just <$> n <|> Nothing <$ wildcard


wildcard :: (Monad p, TokenParsing p) => p ()
wildcard = reserve enameStyle "_"

-- FIXME: patterns
pattern :: (Monad p, PositionParsing p) => p (P.Pattern N.EName)
pattern = spanning
  $   review P.var_ <$> ename
  <|> review P.wildcard_ <$> wildcard
  <|> review P.tuple_ <$> parens (commaSep pattern)
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
  Operator
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
