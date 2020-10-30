module Facet.Notice
( -- * Notices
  Level(..)
, Notice(..)
, level_
, source_
, reason_
, context_
) where

import           Control.Lens (Lens', lens)
import           Facet.Source (Source(..))
import qualified Prettyprinter as P

-- Notices

data Level
  = Info
  | Warn
  | Error
  deriving (Eq, Ord, Show)

instance P.Pretty Level where
  pretty = \case
    Info  -> P.pretty "info"
    Warn  -> P.pretty "warning"
    Error -> P.pretty "error"


data Notice a = Notice
  { level   :: !(Maybe Level)
  -- FIXME: support multiple source references for e.g. cyclic import errors
  , source  :: !(Maybe Source)
  , reason  :: !a
  , context :: ![a]
  }
  deriving (Show)

level_ :: Lens' (Notice a) (Maybe Level)
level_ = lens level $ \ n level -> n{ level }

source_ :: Lens' (Notice a) (Maybe Source)
source_ = lens source $ \ n source -> n{ source }

reason_ :: Lens' (Notice a) a
reason_ = lens reason $ \ n reason -> n{ reason }

context_ :: Lens' (Notice a) [a]
context_ = lens context $ \ n context -> n{ context }
