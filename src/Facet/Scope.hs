{-# LANGUAGE TypeFamilies #-}
module Facet.Scope
( Scope(..)
, decls_
, toList_
) where

import           Control.Monad (guard)
import qualified Data.Map as Map
import           Facet.Name
import           Facet.Syntax
import           Fresnel.Iso
import           Fresnel.Ixed
import           Fresnel.Optional (optional')

newtype Scope a = Scope { decls :: [Name :=: a] }
  deriving (Functor, Monoid, Semigroup)

instance Ixed (Scope a) where
  type Index (Scope a) = Name
  type IxValue (Scope a) = a
  ix n = optional' prj (\ (Scope ds) d' -> Scope (replace (\ (n' :=: _) -> (n' :=: d') <$ guard (n == n')) ds))
    where
    prj = lookup n . map (\ (n :=: a) -> (n, a)) . decls
    replace _ []     = []
    replace f (v:vs) = case f v of
      Nothing -> v:replace f vs
      Just v' -> v':vs

decls_ :: Iso (Scope a) (Scope b) (Map.Map Name a) (Map.Map Name b)
decls_ = toList_.fmapping pair_.iso Map.fromList Map.toList

toList_ :: Iso (Scope a) (Scope b) [Name :=: a] [Name :=: b]
toList_ = coerced
