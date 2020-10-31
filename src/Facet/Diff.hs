module Facet.Diff
( Diff(..)
, Change
) where

import           Control.Monad ((<=<))
import qualified Data.IntMap as IntMap
import           Facet.Name (Meta(..))
import           Facet.Surface

data Diff a b
  = MVar (Ann a)
  | Conc (Ann b)
  deriving (Functor)

type Change f a b = (f b a, f b a)

class Map1 t where
  map1 :: Functor f => (forall x . f x -> g x) -> t f -> t g

instance Map1 Expr where
  map1 f = \case
    Var m n    -> Var m n
    Hole n     -> Hole n
    Type       -> Type
    TInterface -> TInterface
    TString    -> TString
    TComp c    -> TComp (fmap1 f c)
    Lam cs     -> Lam (map1 f <$> cs)
    Thunk r    -> Thunk (fmap1 f r)
    Force r    -> Force (fmap1 f r)

instance Map1 Binding where
  map1 f (Binding p n ds t) = Binding p n (fmap1 f <$> ds) (fmap1 f t)

instance Map1 Clause where
  map1 f (Clause p b) = Clause (fmap1 f p) (fmap1 f b)

instance Map1 Interface where
  map1 f (Interface n sp) = Interface (f n) (fmap1 f <$> sp)

instance Map1 Pattern where
  map1 f = \case
    PWildcard   -> PWildcard
    PVar n      -> PVar n
    PCon n sp   -> PCon n (fmap1 f <$> sp)
    PEff n sp k -> PEff n (fmap1 f <$> sp) k

instance Map1 Comp where
  map1 f (Comp bs ds t) = Comp (fmap1 f <$> bs) (fmap1 f <$> ds) (fmap1 f t)

instance Map1 Decl where
  map1 f (Decl t d) = Decl (fmap1 f t) (map1 f d)

instance Map1 Def where
  map1 f = \case
    DataDef cs      -> DataDef (f . fmap (fmap (fmap1 f)) <$> cs)
    InterfaceDef os -> InterfaceDef (f . fmap (fmap (fmap1 f)) <$> os)
    TermDef t       -> TermDef (fmap1 f t)

instance Map1 Module where
  map1 f (Module n is os ds) = Module n (map f is) os (f . fmap (fmap (fmap1 f)) <$> ds)


fmap1 :: (Map1 t, Functor f) => (forall x . f x -> g x) -> f (t f) -> g (t g)
fmap1 f = f . fmap (map1 f)
