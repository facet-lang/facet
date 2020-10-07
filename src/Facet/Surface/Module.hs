{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Facet.Surface.Module
( Module(..)
, Def(..)
) where

import Facet.Name
import Facet.Surface.Decl (Decl)
import Text.Parser.Position (Span)

-- FIXME: imports
data Module = Module { ann :: Span, name :: MName, defs :: [Def] }

data Def = Def Span DName Decl
