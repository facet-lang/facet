module Facet.Term.Norm
( Norm(..)
, norm
) where

import Control.Monad (guard)
import Data.Foldable (foldl')
import Data.Maybe (fromMaybe)
import Data.Monoid
import Data.Text (Text)
import Data.Traversable (mapAccumL)
import Facet.Env
import Facet.Name
import Facet.Pattern
import Facet.Quote
import Facet.Semialign (zipWithM)
import Facet.Snoc
import Facet.Syntax
import Facet.Term.Expr as X

data Norm
  = NString Text
  | NCon RName [Norm]
  | NLam [(Pattern Name, Pattern (Name :=: Norm) -> Norm)]
  | NNe (Var (LName Level)) (Snoc Norm)
  | NDict [RName :=: Norm]
  | NComp [RName :=: Name] (Pattern (Name :=: Norm) -> Norm)
  deriving (Eq, Ord, Show) via Quoting Expr Norm

instance Quote Norm Expr where
  quote d = \case
    NString s -> X.String s
    NCon n sp -> X.Con n (quote d <$> sp)
    NLam cs   -> X.Lam (map (uncurry clause) cs)
    NNe v sp  -> foldl' (\ h -> X.App h . quote d) (X.Var (fmap (levelToIndex d) <$> v)) sp
    NDict os  -> X.Dict (map (fmap (quote d)) os)
    NComp p b -> X.Comp p (snd (clause (PDict p) b))
    where
    clause p b = let (d', p') = mapAccumL (\ d n -> (succ d, n :=: NNe (Free (LName d n)) Nil)) d p in (p, quote d' (b p'))

norm :: Env Norm -> Expr -> Norm
norm env = \case
  X.String s  -> NString s
  X.Var v     -> NNe (fmap (indexToLevel (level env)) <$> v) Nil
  X.Con n sp  -> NCon n (norm env <$> sp)
  X.App f a   -> norm env f `napp`  norm env a
  X.Lam cs    -> NLam (map (\ (p, b) -> (p, \ p' -> norm (env |> p') b)) cs)
  X.Dict os   -> NDict (map (fmap (norm env)) os)
  X.Let p v b -> norm (env |> fromMaybe (error "norm: non-exhaustive pattern in let") (match (norm env v) p)) b
  X.Comp p b  -> NComp p (\ p' -> norm (env |> p') b)


napp :: Norm -> Norm -> Norm
napp f a = case f of
  NLam cs  -> case getFirst (foldMap (\ (p, b) -> First (b <$> match a p)) cs) of
    Just a' -> a'
    Nothing -> error "napp: non-exhaustive patterns in lambda"
  NNe h sp -> NNe h (sp :> a)
  _        -> error "napp: ill-formed application"

match :: Norm -> Pattern Name -> Maybe (Pattern (Name :=: Norm))
match s = \case
  PWildcard -> Just PWildcard
  PVar n    -> Just (PVar (n :=: s))
  PCon n ps -> case s of
    NCon n' fs -> PCon n' <$ guard (n == n') <*> zipWithM match fs ps
    _          -> Nothing
  PDict ps  -> case s of
    NDict os -> PDict <$> zipWithM (\ (n1 :=: o) (n2 :=: p) -> (n1 :=: (p :=: o)) <$ guard (n1 == n2)) os ps
    _        -> Nothing

-- ninst :: Norm -> T.Type -> Norm
-- ninst f t = case f of
--   NTLam _ b -> b t
--   NNe h sp  -> NNe h (sp :> EInst t)
--   _         -> error "ninst: ill-formed instantiation"
