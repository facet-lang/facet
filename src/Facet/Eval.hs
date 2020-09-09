module Facet.Eval
( Eval(..)
) where

newtype Eval sig a = Eval { eval :: a }
