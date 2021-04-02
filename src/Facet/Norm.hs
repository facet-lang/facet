module Facet.Norm
( Norm(..)
, Elim(..)
, quote
, norm
) where

import           Control.Monad (guard)
import           Data.Foldable (foldl')
import           Data.Function (on)
import           Data.Monoid
import           Data.Text (Text)
import           Data.Traversable (mapAccumL)
import           Facet.Core.Pattern
import           Facet.Core.Term
import qualified Facet.Core.Type as T
import           Facet.Env
import           Facet.Name
import           Facet.Semialign (zipWithM)
import           Facet.Snoc
import           Facet.Syntax

data Norm
  = NString Text
  | NCon RName [Norm]
  | NTLam Name (T.Type -> Norm)
  | NLam [(Pattern Name, Pattern (Name :=: Norm) -> Norm)]
  | NNe (Var (LName Level)) (Snoc Elim)

instance Eq Norm where
  (==) = (==) `on` quote 0

instance Ord Norm where
  compare = compare `on` quote 0

data Elim
  = EApp Norm
  | EInst T.Type


quote :: Level -> Norm -> Expr
quote d = \case
  NString s -> XString s
  NCon n sp -> XCon n (quote d <$> sp)
  NTLam n b -> XTLam n (quote (succ d) (b (T.free (LName d n))))
  NLam cs   -> XLam (map (\ (p, b) -> let (d', p') = mapAccumL (\ d n -> (succ d, n :=: NNe (Free (LName d n)) Nil)) d p in (p, quote d' (b p'))) cs)
  NNe v sp  -> foldl' quoteElim (XVar (fmap (levelToIndex d) <$> v)) sp
  where
  quoteElim h = \case
    EApp n  -> XApp h (quote d n)
    EInst t -> XInst h (T.quote d t)

norm :: Env Norm -> Expr -> Norm
norm env = \case
  XString s -> NString s
  XVar v    -> NNe (fmap (indexToLevel (level env)) <$> v) Nil
  XCon n sp -> NCon n (norm env <$> sp)
  -- FIXME: define type patterns and extend @env@ so we can normalize XTLam correctly
  XTLam _ b -> norm env b
  -- XTLam n b -> NTLam n (\ _T -> norm (env |> pvar (n :=: _T)) b)
  -- FIXME: define type patterns and extend @env@ so we can normalize XInst correctly
  -- FIXME: take a @Subst@ so we can apply substitutions in the type at the same time
  XInst f _ -> norm env f
  -- XInst f t -> norm env f `ninst` T.eval mempty env t
  XApp f a  -> norm env f `napp`  norm env a
  XLam cs   -> NLam (map (\ (p, b) -> (p, \ p' -> norm (env |> p') b)) cs)


napp :: Norm -> Norm -> Norm
napp f a = case f of
  NLam cs  -> case getFirst (foldMap (\ (p, b) -> First (b <$> match a p)) cs) of
    Just a' -> a'
    Nothing -> error "napp: non-exhaustive patterns in lambda"
  NNe h sp -> NNe h (sp :> EApp a)
  _        -> error "napp: ill-formed application"

match :: Norm -> Pattern Name -> Maybe (Pattern (Name :=: Norm))
match s = \case
  PWildcard -> Just PWildcard
  PVar n    -> Just (PVar (n :=: s))
  PCon n ps -> case s of
    NCon n' fs -> PCon n' <$ guard (n == n') <*> zipWithM match fs ps
    _          -> Nothing

-- ninst :: Norm -> T.Type -> Norm
-- ninst f t = case f of
--   NTLam _ b -> b t
--   NNe h sp  -> NNe h (sp :> EInst t)
--   _         -> error "ninst: ill-formed instantiation"
