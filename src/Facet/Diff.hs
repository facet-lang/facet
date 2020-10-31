module Facet.Diff
( Diff(..)
, Change
) where

import Control.Monad ((<=<))
import Facet.Surface

data Diff a b
  = MVar (Ann a)
  | Conc (Ann b)
  deriving (Functor)

type Change f a b = (f b a, f b a)

class Traverse1 t where
  traverse1 :: (Traversable f, Monad m) => (forall x . f x -> m (g x)) -> t f -> m (t g)

instance Traverse1 Expr where
  traverse1 f = \case
    Var m n    -> pure $ Var m n
    Hole n     -> pure $ Hole n
    Type       -> pure $ Type
    TInterface -> pure $ TInterface
    TString    -> pure $ TString
    TComp c    -> TComp <$> ftraverse1 f c
    Lam cs     -> Lam <$> traverse (traverse1 f) cs
    Thunk r    -> Thunk <$> ftraverse1 f r
    Force r    -> Force <$> ftraverse1 f r

instance Traverse1 Binding where
  traverse1 f (Binding p n ds t) = Binding p n <$> traverse (ftraverse1 f) ds <*> ftraverse1 f t

instance Traverse1 Clause where
  traverse1 f (Clause p b) = Clause <$> ftraverse1 f p <*> ftraverse1 f b

instance Traverse1 Interface where
  traverse1 f (Interface n sp) = Interface <$> f n <*> traverse (ftraverse1 f) sp

instance Traverse1 Pattern where
  traverse1 f = \case
    PWildcard   -> pure $ PWildcard
    PVar n      -> pure $ PVar n
    PCon n sp   -> PCon n <$> traverse (ftraverse1 f) sp
    PEff n sp k -> PEff n <$> traverse (ftraverse1 f) sp <*> pure k

instance Traverse1 Comp where
  traverse1 f (Comp bs ds t) = Comp <$> traverse (ftraverse1 f) bs <*> traverse (ftraverse1 f) ds <*> ftraverse1 f t

instance Traverse1 Decl where
  traverse1 f (Decl t d) = Decl <$> ftraverse1 f t <*> traverse1 f d

instance Traverse1 Def where
  traverse1 f = \case
    DataDef cs      -> DataDef <$> traverse (f <=< traverse (traverse (ftraverse1 f))) cs
    InterfaceDef os -> InterfaceDef <$> traverse (f <=< traverse (traverse (ftraverse1 f))) os
    TermDef t       -> TermDef <$> ftraverse1 f t

instance Traverse1 Module where
  traverse1 f (Module n is os ds) = Module n <$> traverse f is <*> pure os <*> traverse (f <=< traverse (traverse (ftraverse1 f))) ds


ftraverse1 :: (Traverse1 t, Traversable f, Monad m) => (forall x . f x -> m (g x)) -> f (t f) -> m (g (t g))
ftraverse1 f = f <=< traverse (traverse1 f)
