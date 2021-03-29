module Facet.Norm
( Norm(..)
, Elim(..)
, quote
) where

import           Data.Foldable (foldl')
import           Data.Text (Text)
import           Data.Traversable (mapAccumL)
import           Facet.Core.Pattern
import           Facet.Core.Term
import qualified Facet.Core.Type as T
import           Facet.Name
import           Facet.Snoc
import           Facet.Syntax

data Norm
  = NString Text
  | NCon RName (Snoc Norm)
  | NTLam Name (T.Type -> Norm)
  | NLam [(Pattern Name, Pattern (Name :=: Norm) -> Norm)]
  | NNe (Var (LName Level)) (Snoc Elim)

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
