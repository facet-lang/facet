module Facet.Term.Norm
( Term(..)
, norm
) where

import           Control.Monad (guard)
import           Data.Foldable (foldl')
import           Data.Maybe (fromMaybe)
import           Data.Monoid
import           Data.Text (Text)
import           Facet.Env
import           Facet.Name
import           Facet.Pattern
import           Facet.Quote
import           Facet.Semialign (zipWithM)
import           Facet.Snoc
import           Facet.Syntax
import qualified Facet.Term.Expr as X

data Term
  = String Text
  | Con QName [Term]
  | Lam [(Pattern Name, Pattern (Name :=: Term) -> Term)]
  | Ne (Var Level) (Snoc Term)
  deriving (Eq, Ord, Show) via Quoting X.Term Term

instance Quote Term X.Term where
  quote = \case
    String s -> pure (X.String s)
    Con n sp -> X.Con n <$> traverse quote sp
    Lam cs   -> X.Lam <$> traverse (uncurry clause) cs
    Ne v sp  -> foldl' (\ h t -> X.App <$> h <*> quote t) (Quoter (\ d -> X.Var (toIndexed d v))) sp
    where
    clause :: Traversable t => t Name -> (t (Name :=: Term) -> Term) -> Quoter (t Name, X.Term)
    clause p b = Quoter (\ d -> let (d', p') = mapAccumLevels (\ d n -> n :=: Ne (Bound d) Nil) d p in (p, runQuoter d' (quote (b p'))))

norm :: Env Term -> X.Term -> Term
norm env = \case
  X.String s  -> String s
  X.Var v     -> Ne (toLeveled (level env) v) Nil
  X.Con n sp  -> Con n (norm env <$> sp)
  X.App f a   -> norm env f `napp`  norm env a
  X.Lam cs    -> Lam (map (\ (p, b) -> (p, \ p' -> norm (foldl' (|>) env p') b)) cs)
  X.Let p v b -> norm (foldl' (|>) env (fromMaybe (error "norm: non-exhaustive pattern in let") (match (norm env v) p))) b


napp :: Term -> Term -> Term
napp f a = case f of
  Lam cs  -> case getFirst (foldMap (\ (p, b) -> First (b <$> match a p)) cs) of
    Just a' -> a'
    Nothing -> error "napp: non-exhaustive patterns in lambda"
  Ne h sp -> Ne h (sp :> a)
  _       -> error "napp: ill-formed application"

match :: Term -> Pattern Name -> Maybe (Pattern (Name :=: Term))
match s = \case
  PVal p -> PVal <$> val s p
  PEff _ -> Nothing
  where
  val s = \case
    PWildcard -> Just PWildcard
    PVar n    -> Just (PVar (n :=: s))
    PCon n ps -> case s of
      Con n' fs -> PCon n' <$ guard (n == n') <*> zipWithM val fs ps
      _         -> Nothing

-- ninst :: Term -> T.Type -> Term
-- ninst f t = case f of
--   NTLam _ b -> b t
--   NNe h sp  -> NNe h (sp :> EInst t)
--   _         -> error "ninst: ill-formed instantiation"
