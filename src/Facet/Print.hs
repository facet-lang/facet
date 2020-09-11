{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
module Facet.Print
( Print(..)
) where

import           Data.Kind (Type)
import qualified Data.Text.Prettyprint.Doc as PP
import           Facet.Expr

newtype Print (sig :: Bin (Type -> Type)) a = Print { print :: PP.Doc () }
