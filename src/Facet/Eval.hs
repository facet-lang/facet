module Facet.Eval
( eval
) where

import Control.Effect.Reader
import Facet.Core hiding (eval)
import Facet.Env as E
import Facet.Syntax

-- FIXME: erase terms before evaluating.
eval :: Has (Reader (Env Value)) sig m => Value -> m Value
eval = \case
  VNeut h sp -> do
    sp' <- traverse evalSp sp
    env <- ask
    case h of
      Global (q ::: _)
        | Just (Just v ::: _) <- E.lookupQ @Value q env
        -> pure $ elimN v sp'
      _ -> pure $ VNeut h sp'

  v          -> pure v
  where
  evalSp = \case
    EApp a -> EApp <$> traverse eval a
    e      -> pure e
