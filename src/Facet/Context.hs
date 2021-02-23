module Facet.Context
( -- * Contexts
  Quantity
, Context(..)
, Binding(..)
, VarType(..)
, empty
, (|>)
, level
, (!)
, lookupIndex
, toEnv
) where

import qualified Control.Applicative as Alt
import           Data.Semialign
import           Facet.Core.Type
import           Facet.Name
import           Facet.Semiring
import qualified Facet.Snoc as S
import           Facet.Syntax
import           Facet.Usage
import           GHC.Stack
import           Prelude hiding (lookup, zipWith)

newtype Context = Context { elems :: S.Snoc Binding }

-- | A precondition for use of this instance is that one only ever '<>'s 'Context's assigning the same types to the same variables in the same order.
instance Semigroup Context where
  Context e1 <> Context e2 = Context (zipWith (<>) e1 e2)

instance LeftModule Quantity Context where
  q ><< Context e = Context ((q ><<) <$> e)

data Binding = Binding
  { name     :: Name
  , quantity :: Quantity
  , type'    :: Type P
  }

data VarType
  = Tm (Type P)
  | Ty (Type T)

-- | A precondition for use of this instance is that one only ever '<>'s pairs of 'Binding's assigning the same type to the same variable.
instance Semigroup Binding where
  Binding _ q1 _ <> Binding n q2 _T = Binding n (q1 <> q2) _T

instance LeftModule Quantity Binding where
  q1 ><< Binding n q2 _T = Binding n (q1 >< q2) _T

empty :: Context
empty = Context S.Nil

(|>) :: Context -> Binding -> Context
Context as |> a = Context (as S.:> a)

infixl 5 |>

level :: Context -> Level
level (Context es) = Level (length es)

(!) :: HasCallStack => Context -> Index -> Binding
Context es' ! Index i' = withFrozenCallStack $ go es' i'
  where
  go (es S.:> e) i
    | i == 0       = e
    | otherwise    = go es (i - 1)
  go _           _ = error $ "Facet.Context.!: index (" <> show i' <> ") out of bounds (" <> show (length es') <> ")"

lookupIndex :: Alt.Alternative m => Name -> Context -> m (Index, Quantity, Type P)
lookupIndex n = go (Index 0) . elems
  where
  go _ S.Nil            = Alt.empty
  go i (cs S.:> Binding n' q t)
    | n == n'           = pure (i, q, t)
    | otherwise         = go (succ i) cs


-- | Construct an environment suitable for evaluation from a 'Context'.
toEnv :: Context -> S.Snoc (Type P)
toEnv c = locals 0 (elems c)
  where
  d = level c
  locals i = \case
    S.Nil     -> S.Nil
    bs S.:> _ -> locals (succ i) bs S.:> free (indexToLevel d i)
