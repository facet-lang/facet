module Facet.Notice
( -- * Notices
  Level(..)
, Notice(..)
, level_
, source_
, reason_
, context_
, reAnnotateNotice
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
  , reason  :: !(P.Doc a)
  , context :: ![P.Doc a]
  }
  deriving (Show)

level_ :: Lens' (Notice a) (Maybe Level)
level_ = lens level $ \ n level -> n{ level }

source_ :: Lens' (Notice a) (Maybe Source)
source_ = lens source $ \ n source -> n{ source }

reason_ :: Lens' (Notice a) (P.Doc a)
reason_ = lens reason $ \ n reason -> n{ reason }

context_ :: Lens' (Notice a) [P.Doc a]
context_ = lens context $ \ n context -> n{ context }

reAnnotateNotice :: (a -> b) -> (Notice a -> Notice b)
reAnnotateNotice f Notice{ level, source, reason, context} = Notice{ level, source, reason = P.reAnnotate f reason, context = map (P.reAnnotate f) context }
