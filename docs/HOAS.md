# HOAS

I keep forgetting the relative benefits and limitations of variations on HOAS, so I’m writing them here to remind myself.


## Closed

```haskell
data Type
  = Type
  | ForAll Type (Type -> Type)
  | App Type Type
```

- ✅ always scope-safe
- ❌ can’t unify
- ❌ can’t fold without unfold
- ❌ can’t represent open terms
- ❌ “exotic” terms


## Open (polymorphic)

```haskell
data Type a
  = Free a
  | Type
  | ForAll (Type a) (Type a -> Type a)
  | App (Type a) (Type a)
```

- ✅ scope-safety is obvious from the type (e.g. `Type Void` is closed, as is `forall x . Type x`)
- ✅ can fold by stashing results in `Free` constructor
- ❌ unification requires building the body outside of the binder, and then substituting for the bound variable inside of it
- ❌ thus, unification requires picking a domain for the variables
- ❌ can’t close once opened, or at least, not easily
- ❌ can’t close when built under a monad
- ❌ “exotic” terms


## Open (de Bruijn levels/indices)

```haskell
data Type
  = Free Level
  | Type
  | ForAll Type (Type -> Type)
  | App Type Type
```

- ✅ can fold by stashing results in a context and referencing the corresponding level in the `Free` constructor
- ✅ operations (e.g. unification) don’t fix a specific variable domain because it’s always fixed at `Level`, so this doesn’t make it harder to pretty-print
- ❌ scope-safety is not obvious from the type
- ❌ incorrect levels ⇒ 💥
- ❌ unification requires building the body outside of the binder, and then substituting for the bound variable inside of it
- ❌ can’t close, period
- ❌ “exotic” terms


## Open (polymorphic), effects

```haskell
data Type a
  = Free a
  | Type
  | ForAll (Type a) (Type a -> Maybe (Type a))
  | App (Type a) (Type a)
```

- ✅ scope-safety is obvious from the type (e.g. `Type Void` is closed, as is `forall x . Type x`)
- ✅ can fold by stashing results in `Free` constructor
- ✅ unification can occur under the binder, without having to pick a domain or substitute
- ❌ can’t close once opened, or at least, not easily
- ❌ can’t close when built under a monad
- ❌ no way to tell if it’s total or not; errors could be hiding under binders
- ❌ (almost?) impossible to eliminate possibility of failure under binders by e.g. rebuilding w/ `Identity`
- ❌ “exotic” terms
