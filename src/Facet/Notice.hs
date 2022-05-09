module Facet.Notice
( -- * Notices
  Level(..)
, Notice(..)
, level_
, references_
, reason_
, context_
) where

import Facet.Source (Source(..))
import Fresnel.Lens (Lens', lens)

-- Notices

data Level
  = Info
  | Warn
  | Error
  deriving (Eq, Ord, Show)

data Notice a = Notice
  { level      :: !(Maybe Level)
  -- FIXME: support multiple source references for e.g. cyclic import errors
  , references :: ![Source]
  , reason     :: !a
  , context    :: ![a]
  }
  deriving (Functor, Show)

level_ :: Lens' (Notice a) (Maybe Level)
level_ = lens level $ \ n level -> n{ level }

references_ :: Lens' (Notice a) [Source]
references_ = lens references $ \ n references -> n{ references }

reason_ :: Lens' (Notice a) a
reason_ = lens reason $ \ n reason -> n{ reason }

context_ :: Lens' (Notice a) [a]
context_ = lens context $ \ n context -> n{ context }
