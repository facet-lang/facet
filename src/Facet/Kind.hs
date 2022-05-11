module Facet.Kind
( -- * Kinds
  Kind(..)
, _KType
, _KInterface
, _KArrow
  -- * Constructors
, (==>)
) where

import Facet.Name
import Fresnel.Prism (Prism', prism')

-- Kinds

data Kind
  = KType
  | KInterface
  | KArrow (Maybe Name) Kind Kind
  deriving (Eq, Ord, Show)

_KType :: Prism' Kind ()
_KType = prism' (const KType) (\case{ KType -> Just () ; _ -> Nothing })

_KInterface :: Prism' Kind ()
_KInterface = prism' (const KInterface) (\case{ KInterface -> Just () ; _ -> Nothing })

_KArrow :: Prism' Kind (Maybe Name, Kind, Kind)
_KArrow = prism' (\ (n, a, b) -> KArrow n a b) (\case{ KArrow n a b -> Just (n, a, b) ; _ -> Nothing })


-- Constructors

(==>) :: Kind -> Kind -> Kind
(==>) = KArrow Nothing
infixr 1 ==>
