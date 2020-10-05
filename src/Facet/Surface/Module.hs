{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Facet.Surface.Module
( Module(..)
, module'
, defTerm
, defType
, ModuleF(..)
, fold
) where

import Facet.Name
import Facet.Surface.Decl (Decl)
import Text.Parser.Position (Spanned(..), Span)

newtype Module = In { out :: ModuleF Module }

instance Spanned Module where
  setSpan = fmap In . Loc

module' :: MName -> [Module] -> Module
module' = fmap In . Module

defTerm :: EName -> Decl -> Module
defTerm = fmap In . DefTerm

defType :: TName -> Decl -> Module
defType = fmap In . DefType

data ModuleF a
  = Module MName [a]
  | DefTerm EName Decl
  | DefType TName Decl
  | Loc Span a
  deriving (Foldable, Functor, Traversable)


fold :: (ModuleF a -> a) -> Module -> a
fold alg = go
  where
  go = alg . fmap go . out
