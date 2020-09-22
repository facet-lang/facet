module Facet.Elab
( Elab(..)
) where

import Facet.Type

newtype Elab = Elab { runElab :: Type -> () }
