{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Facet.Surface.Name
( EName(..)
) where

import Data.String (IsString(..))
import Data.Text (Text)
import Prettyprinter (Pretty)

newtype EName = EName { getEName :: Text }
  deriving (Eq, IsString, Ord, Pretty, Show)
