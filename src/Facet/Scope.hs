{-# LANGUAGE TypeFamilies #-}
module Facet.Scope
( Scope(..)
, decls_
, toList_
  -- * Eliminators
, lookupIndex
) where

import           Control.Monad (guard)
import           Data.List (findIndex)
import qualified Data.Map as Map
import           Facet.Name
import           Facet.Syntax
import           Fresnel.Getter (view)
import           Fresnel.Iso
import           Fresnel.Ixed
import           Fresnel.Optional (optional')
import           GHC.Exts (IsList(..))

newtype Scope a = Scope { decls :: [Name :=: a] }
  deriving (Functor, Monoid, Semigroup)

instance Ixed (Scope a) where
  type Index (Scope a) = Name
  type IxValue (Scope a) = a
  ix n = optional' prj (\ (Scope ds) d' -> Scope (replace (\ (n' :=: _) -> (n' :=: d') <$ guard (n == n')) ds))
    where
    prj = lookup n . map (view pair_) . decls
    replace _ []     = []
    replace f (v:vs) = case f v of
      Nothing -> v:replace f vs
      Just v' -> v':vs

instance IsList (Scope a) where
  type Item (Scope a) = Name :=: a
  fromList = Scope
  toList = decls

decls_ :: Iso (Scope a) (Scope b) (Map.Map Name a) (Map.Map Name b)
decls_ = toList_.fmapping pair_.iso Map.fromList Map.toList

toList_ :: Iso (Scope a) (Scope b) [Name :=: a] [Name :=: b]
toList_ = coerced


-- Eliminators

lookupIndex :: Name -> Scope a -> Maybe Int
lookupIndex n = findIndex (\ (n' :=: _) -> n == n') . decls
