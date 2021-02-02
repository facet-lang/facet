module Facet.Core.Term
( -- * Term variables
  Var(..)
  -- * Patterns
, ValuePattern(..)
, Pattern(..)
, pvar
, pcon
, fill
  -- * Term values
, Value(..)
, Elim(..)
, global
, free
, var
  -- ** Elimination
, ($$)
, ($$*)
, ($$$)
, ($$$*)
  -- ** Debugging
, showValue
  -- * Term expressions
, Expr(..)
  -- * Quotation
, quote
, eval
) where

import           Control.Monad (guard)
import           Data.Foldable (asum, foldl')
import           Data.Semialign.Exts (zipWithM)
import           Data.Text (Text)
import           Data.Traversable (mapAccumL)
import qualified Facet.Core.Type as T
import           Facet.Name
import           Facet.Pretty (toAlpha)
import           Facet.Show
import           Facet.Stack
import           Facet.Syntax
import           GHC.Stack

-- Term variables

data Var a
  = Global (Q Name) -- ^ Global variables, considered equal by 'Q' 'Name'.
  | Free a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)


-- Patterns

data ValuePattern a
  = PWildcard
  | PVar a
  | PCon (Q Name :$ ValuePattern a)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

data Pattern a
  -- FIXME: pretty sure the sub-patterns should be ValuePatterns instead
  = PEff (Q Name) (Stack (Pattern a)) a
  | PAll a
  | PVal (ValuePattern a)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

pvar :: a -> Pattern a
pvar = PVal . PVar

pcon :: Q Name :$ ValuePattern a -> Pattern a
pcon = PVal . PCon


fill :: Traversable t => (b -> (b, c)) -> b -> t a -> (b, t c)
fill f = mapAccumL (const . f)


-- Term values

data Value
  = VTLam (T.Type -> Value)
  | VLam [(Pattern Name, Pattern Value -> Value)]
  | VNe (Var Level :$ T.Type :$ Value)
  | VCon (Q Name :$ Value)
  | VString Text
  | VOp (Q Name :$ T.Type :$ Value)

data Elim
  = EInst T.Type
  | EApp Value


global :: Q Name -> Value
global = var . Global

free :: Level -> Value
free = var . Free


var :: Var Level -> Value
var = VNe . (:$ Nil) . (:$ Nil)


-- Elimination

($$) :: HasCallStack => Value -> Value -> Value
($$) = app 0

app :: HasCallStack => Level -> Value -> Value -> Value
app _ (VNe (h :$ ts :$ es)) a = VNe (h :$ ts :$ (es :> a))
app _ (VLam cs)             a = case' a cs
app _ (VTLam _)             _ = error "can’t apply type lambda"
app d (VCon (q :$ fs))      _ = error $ "can’t apply constructor " <> appEndo (showValue Nil Nil d 0 (VCon (q :$ fs))) ""
app _ (VString _)           _ = error "can’t apply string"
app _ (VOp (h :$ es))       a = VOp (h :$ (es :> a))

($$*) :: (HasCallStack, Foldable t) => Value -> t Value -> Value
($$*) = foldl' ($$)

infixl 9 $$, $$*


($$$) :: HasCallStack => Value -> T.Type -> Value
VNe (h :$ ts :$ es) $$$ t = VNe (h :$ (ts :> t) :$ es)
VTLam b             $$$ t = b t
VLam _              $$$ _ = error "can’t instantiate lambda"
VCon (q :$ _)       $$$ _ = error $ "can’t instantiate constructor " <> show q
VString _           $$$ _ = error "can’t instantiate string"
VOp (h :$ ts :$ es) $$$ t = VOp (h :$ (ts :> t) :$ es)

($$$*) :: (HasCallStack, Foldable t) => Value -> t T.Type -> Value
($$$*) = foldl' ($$$)

infixl 9 $$$, $$$*


case' :: HasCallStack => Value -> [(Pattern Name, Pattern Value -> Value)] -> Value
case' s cs = case asum (map (\ (p, f) -> f <$> match s p) cs) of
  Just v -> v
  _      -> error "non-exhaustive patterns in lambda"

match :: Value -> Pattern b -> Maybe (Pattern Value)
match = curry $ \case
  (s, PAll _)  -> Just (PAll s)
  -- FIXME: match effect patterns against computations (?)
  (_, PEff{})  -> Nothing
  (s, PVal p') -> PVal <$> value s p'
  where
  value = curry $ \case
    (_,               PWildcard)      -> Just PWildcard
    (s,               PVar _)         -> Just (PVar s)
    -- NB: we’re assuming they’re the same length because they’ve passed elaboration.
    (VCon (n' :$ fs), PCon (n :$ ps)) -> PCon . (n' :$) <$ guard (n == n') <*> zipWithM value fs ps
    (_, PCon{})                       -> Nothing


-- Debugging

showValue :: HasCallStack => Stack (Endo String) -> Stack (Endo String) -> Level -> Int -> Value -> Endo String
showValue tenv env d p = \case
  VTLam b             -> brace (brace (string (toAlpha alpha (length tenv))) <+> string "->" <+> showValue (tenv :> string (toAlpha alpha (length tenv))) env (succ d) 0 (b (T.free d)))
  VLam cs             -> brace (commaSep (map clause cs))
  VNe (f :$ ts :$ sp) -> parenIf (p > 10) $ foldl' (<+>) (foldl' (<+>) (head f) (T.showType tenv 11 <$> ts)) (showValue tenv env d 11 <$> sp)
  VCon (q :$ fs)      -> parenIf (p > 10) $ foldl' (<+>) (qname q) (showValue tenv env d 11 <$> fs)
  VString s           -> text s
  VOp (f :$ ts :$ sp) -> parenIf (p > 10) $ foldl' (<+>) (foldl' (<+>) (qname f) (T.showType tenv 11 <$> ts)) (showValue tenv env d 11 <$> sp)
  where
  clause (p, b) = pat p <+> string "->" <+> showValue tenv env' d 0 (b p')
    where
    ((env', _), p') = mapAccumL (\ (env, d) n -> ((env :> name n, succ d), free d)) (env, d) p
  pat = \case
    PAll n      -> bracket (name n)
    PVal p      -> vpat p
    PEff n ps k -> bracket (foldl' (<+>) (qname n) (pat <$> ps) <+> char ';' <+> name k)
  vpat = \case
    PWildcard      -> char '_'
    PVar n         -> name n
    PCon (f :$ ps) -> paren $ foldl' (<+>) (qname f) (vpat <$> ps)
  alpha = ['A'..'Z']
  head = \case
    Global (m :.: n) -> foldr (<.>) (name n) (text <$> m)
    Free v           -> env ! getIndex (levelToIndex d v)


-- Term expressions

data Expr
  = XVar (Var Index)
  | XTLam Expr
  | XLam [(Pattern Name, Expr)]
  | XInst Expr T.TExpr
  | XApp Expr Expr
  | XCon (Q Name :$ Expr)
  | XString Text
  | XOp (Q Name)
  deriving (Eq, Ord, Show)


-- Quotation

quote :: Level -> Value -> Expr
quote d = \case
  VTLam b             -> XTLam (quote (succ d) (b (T.free d)))
  VLam cs             -> XLam (map (\ (p, b) -> (p, let (d', p') = fill (\ d -> (succ d, free d)) d p in quote d' (b p'))) cs)
  VNe (h :$ ts :$ as) -> let h' = XVar (levelToIndex d <$> h) ; h'' = foldl' XInst h' (T.quote d <$> ts) in foldl' XApp h'' (quote d <$> as)
  VCon (n :$ fs)      -> XCon (n :$ (quote d <$> fs))
  VString s           -> XString s
  VOp (n :$ ts :$ sp) -> foldl' XApp (foldl' XInst (XOp n) (T.quote d <$> ts)) (quote d <$> sp)

eval :: HasCallStack => T.Subst -> Stack T.Type -> Expr -> Value
eval subst tenv = go tenv Nil where
  go tenv env = \case
    XVar (Global n) -> global n
    XVar (Free v)   -> env ! getIndex v
    XTLam b         -> VTLam (\ _T -> go (tenv :> _T) env b)
    XLam cs         -> VLam (map (\ (p, b) -> (p, \ p -> go tenv (foldl' (:>) env p) b)) cs)
    XInst f a       -> go tenv env f $$$ T.eval subst tenv a
    XApp  f a       -> go tenv env f $$ go tenv env a
    XCon (n :$ fs)  -> VCon (n :$ (go tenv env <$> fs))
    XString s       -> VString s
    XOp n           -> VOp (n :$ Nil :$ Nil)
