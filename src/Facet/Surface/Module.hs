{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Facet.Surface.Module
( Module(..)
, module'
, def
, ModuleF(..)
, fold
) where

import Control.Category ((>>>))
import Facet.Name
import Facet.Surface.Decl (Decl)
import Text.Parser.Position (Span, Spanned(..))

newtype Module = In { out :: ModuleF Module }

instance Spanned Module where
  setSpan = fmap In . Loc

  dropSpan = out >>> \case
    Loc _ d -> dropSpan d
    d       -> In d

module' :: MName -> [Module] -> Module
module' = fmap In . Module

def :: DName -> Decl -> Module
def = fmap In . Def

data ModuleF a
  = Module MName [a]
  | Def DName Decl
  | Loc Span a
  deriving (Foldable, Functor, Traversable)


fold :: (ModuleF a -> a) -> Module -> a
fold alg = go
  where
  go = alg . fmap go . out
