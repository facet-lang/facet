module Facet.Core.Term
( -- * Term variables
  Var(..)
, unVar
  -- * Term values
, Value(..)
, Elim(..)
, global
, free
, var
  -- ** Elimination
, ($$)
, ($$*)
  -- * Term expressions
, Expr(..)
  -- * Quotation
, quote
, eval
) where

import           Control.Monad (guard)
import           Data.Foldable (asum, foldl')
import qualified Data.IntMap as IntMap
import           Data.Semialign.Exts (zipWithM)
import           Data.Text (Text)
import           Facet.Core
import qualified Facet.Core.Type as T
import           Facet.Name
import           Facet.Stack
import           Facet.Syntax
import           GHC.Stack

-- Term variables

data Var a
  = Global (Q Name) -- ^ Global variables, considered equal by 'QName'.
  | Free a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

unVar :: (Q Name -> b) -> (a -> b) -> Var a -> b
unVar f g = \case
  Global  n -> f n
  Free    n -> g n


-- Term values

data Value
  = VTLam (T.Type -> Value)
  | VLam [(Pattern Name, Pattern Value -> Value)]
  | VNe (Var Level :$ Elim)
  | VCon (Q Name :$ Value)
  | VString Text
  | VOp (Q Name :$ Value)

data Elim
  = EInst T.Type
  | EApp Value


global :: Q Name -> Value
global = var . Global

free :: Level -> Value
free = var . Free


var :: Var Level -> Value
var = VNe . (:$ Nil)


-- Elimination

($$) :: HasCallStack => Value -> Elim -> Value
VNe (h :$ es) $$ a       = VNe (h :$ (es :> a))
VTLam b       $$ EInst a = b a
VLam cs       $$ EApp  a = case' a cs
_             $$ _       = error "can’t apply non-neutral/lambda value"

($$*) :: (HasCallStack, Foldable t) => Value -> t Elim -> Value
($$*) = foldl' ($$)

infixl 9 $$, $$*


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


-- Term expressions

data Expr
  = XVar (Var Index)
  | XTLam Expr
  | XLam [(Pattern Name, Expr)]
  | XInst Expr T.TExpr
  | XApp Expr Expr
  | XCon (Q Name :$ Expr)
  | XString Text
  | XOp (Q Name) -- FIXME: this should have the arguments
  deriving (Eq, Ord, Show)


-- Quotation

quote :: Level -> Value -> Expr
quote d = \case
  VTLam b        -> XTLam (quote (succ d) (b (T.free d)))
  VLam cs        -> XLam (map (\ (p, b) -> (p, let (d', p') = fill (\ d -> (succ d, free d)) d p in quote d' (b p'))) cs)
  VNe (h :$ sp)  -> foldl' (\ head -> \case
    EInst _T -> XInst head (T.quote d _T)
    EApp a   -> XApp head (quote d a)) (XVar (levelToIndex d <$> h)) sp
  VCon (n :$ fs) -> XCon (n :$ (quote d <$> fs))
  VString s      -> XString s
  VOp (n :$ sp)  -> foldl' XApp (XOp n) (quote d <$> sp)

eval :: HasCallStack => IntMap.IntMap T.Type -> Expr -> Value
eval subst = go Nil Nil where
  go tenv env = \case
    XVar v         -> unVar global ((env !) . getIndex) v
    XTLam b        -> VTLam (\ _T -> go (tenv :> _T) env b)
    XLam cs        -> VLam (map (\ (p, b) -> (p, \ p -> go tenv (foldl' (:>) env p) b)) cs)
    XInst f a      -> go tenv env f $$ EInst (T.eval subst tenv a)
    XApp  f a      -> go tenv env f $$ EApp (go tenv env a)
    XCon (n :$ fs) -> VCon (n :$ (go tenv env <$> fs))
    XString s      -> VString s
    XOp n          -> VOp (n :$ Nil)
