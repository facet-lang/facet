module Facet.Core.Term
( -- * Term variables
  Var(..)
, unVar
  -- * Term values
, Value(..)
, global
, free
, var
  -- * Term expressions
, Expr(..)
) where

import Data.Text (Text)
import Facet.Core
import Facet.Core.Type
import Facet.Name
import Facet.Syntax

-- Term variables

data Var a
  = Global (Q Name) -- ^ Global variables, considered equal by 'QName'.
  | Free a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

unVar :: (Q Name -> b) -> (a -> b) -> Var a -> b
unVar f g = \case
  Global  n -> f n
  Free    n -> g n


-- Term values

data Value
  = VTLam (Type -> Value)
  | VLam [(Pattern Name, Pattern Value -> Value)]
  | VNe (Var Level :$ Either Type Value)
  | VCon (Q Name :$ Value)
  | VString Text
  | VOp (Q Name :$ Value)


global :: Q Name -> Value
global = var . Global

free :: Level -> Value
free = var . Free


var :: Var Level -> Value
var = VNe . (:$ Nil)


-- Term expressions

data Expr
  = XVar (Var Index)
  | XTLam Expr
  | XLam [(Pattern Name, Expr)]
  | XInst Expr TExpr
  | XApp Expr Expr
  | XCon (Q Name :$ Expr)
  | XString Text
  | XOp (Q Name) -- FIXME: this should have the arguments
  deriving (Eq, Ord, Show)
