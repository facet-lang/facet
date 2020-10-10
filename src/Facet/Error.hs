module Facet.Error
( ErrDoc
, Err(..)
, ErrM
, runErrM
) where

import Control.Effect.Parser.Span (Span)
import Data.Functor.Identity
import Facet.Carrier.Error.Context
import Prettyprinter (Doc)
import Prettyprinter.Render.Terminal (AnsiStyle)

type ErrDoc = Doc AnsiStyle

data Err = Err
  { reason  :: ErrDoc
  , context :: [ErrDoc]
  }
  deriving (Show)

type ErrM = ErrorC Span Err Identity

runErrM :: Span -> ErrorC Span Err Identity a -> Either (Span, Err) a
runErrM s = run . runError (curry (Identity . Left)) (Identity . Right) s
