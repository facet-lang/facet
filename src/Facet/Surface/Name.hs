{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Facet.Surface.Name
( EName(..)
, TName(..)
) where

import Data.String (IsString(..))
import Data.Text (Text)
import Prettyprinter (Pretty)

newtype EName = EName { getEName :: Text }
  deriving (Eq, IsString, Ord, Pretty, Show)

newtype TName = TName { getTName :: Text }
  deriving (Eq, IsString, Ord, Pretty, Show)
