# HOAS

I keep forgetting the relative benefits and limitations of variations on HOAS, so I’m writing them here to remind myself.


## Closed, no effects

```haskell
data Type
  = KType
  | TForAll Type (Type -> Type)
  | TApp Type Type
```

- ✅ always scope-safe
- ❌ can’t unify
- ❌ can’t fold without unfold
- ❌ can’t represent open terms


## Open (polymorphic), no effects

```haskell
data Type a
  = VFree a
  | KType
  | TForAll (Type a) (Type a -> Type a)
  | TApp (Type a) (Type a)
```

- ✅ scope-safety is obvious from the type (e.g. `Type Void` is closed, as is `forall x . Type x`)
- ✅ can fold by stashing results in `VFree` constructor
- ❌ unification requires building the body outside of the binder, and then substituting for the bound variable inside of it
- ❌ thus, unification requires picking a domain for the variables
- ❌ can’t close once opened, or at least, not easily
- ❌ can’t close when built under a monad
