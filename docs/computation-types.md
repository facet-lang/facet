# Computation types

## Frank

In Frank, arrow types (e.g. for higher-order functions) are written in curly braces indicating that they’re computations; a function signature is implicitly a computation without requiring braces; and nullary computations can be written with an ! on the lhs to indicate that it’s a computation and not a value.

Thus, they have:

```frank
interface Abort = aborting : Zero
abort : [Abort]X
abort! = on aborting! {}
```

as an example both of constructing and eliminating nullary computations. (As the paper notes, we can see from this that while `Zero` is uninhabited, `{[Abort]Zero}` is inhabited.)

Thus we could write:

```frank
modify : {S -> S} -> [State S]Unit
modify f = put (f get!)
```

or, equivalently:

```frank
modify : { {S -> S} -> [State S]Unit }
modify f = put (f get!)
```

(I’m not sure that the effect name would go there in this case.) It’s not clear to me why the arrow forms a computation. I suppose it allows you to avoid writing a bunch of postfix bangs in places that might otherwise be required, e.g. following the arguments to put, and which would be of ambiguous precedence if one weren’t careful. Likewise, they’re careful to avoid allowing the implicit coercion of {A} to A; the postfix ! is necessary to force evaluation. On the other hand, it does appear that they allow implicit coercion of A to {A} without any additional plumbing (`return` in Haskell comes to mind, and is specifically mentioned in the paper).


# Facet

By contrast, I want to think of computations as a unary type former. _Edit: this is no longer true, following a bunch of reading up on CBPV and focusing._

```
 Γ ⊢ A : Type
--------------
Γ ⊢ {A} : Type
```

One reason for this is that I want to explore effectful staged computation, and thus to be able to distinguish between the effects necessary to _construct_ a function and the effects necessary to _run_ a function. In particular, this has implications for partial evaluation: A -> B -> {C} (for some signature, irrelevant at the moment) can compute—and hence signal any kind of response—only once both arguments are supplied (and the computation is forced), whereas A -> {B -> C} could respond as soon as the first argument is supplied, and {A -> B -> C} can’t be called at all without potentially provoking a response.

However, we have to be careful to control the context in which effects are performed. An implicitly effect-polymorphic function like `map` runs its higher-order function eagerly, and thus only performs the effects available in the calling context, and does so at once.

So what about `Coyoneda`?

```haskell
data Coyoneda f a where
  Coyoneda :: (a -> b) -> f a -> Coyoneda f b
```

Leaving aside the question of existentials for the moment, are effects latent in `(a -> b)` performed at the point of construction, or the point of elimination?

Another example is performing effects under binders with HOAS. For example, parsing into a HOAS structure is notoriously tricky, and unifying under one is even more so—in the former case, you can do some tricks along the lines of `Distributive` to ensure that you get a pure function out, but in the latter you can only unify once a value for the variable has been supplied. Adding in questions of variance, and it becomes extremely difficult to use. Haskell distinguishes `m (a -> a)` from `(a -> m a)`; it’s not clear to me whether Frank does.

Really, the HOAS I use in Haskell is too strong—cf the problem of so-called “exotic terms.” But weak HOAS—e.g. PHOAS—is _too_ weak; it doesn’t admit hereditary substitution, for example, as far as I can tell.

I need fast, bulletproof substitution, or I wouldn’t be using HOAS at all. But given two binders, e.g. quantifiers, I need to be able to ask if, given the same (arbitrary) argument type, they produce the same result type. Any well-typed choice of argument will do, because if they’re not exotic, they can’t behave uniquely with respect to it anyway—they truly are defined the same _for all_ argument types. So as long as we make the same choice for both sides, we should deterministically arrive at the same result for both sides _iff_ they are the same—that’s the definition of definitional equality.

In other words, given `Type -> [Err]{Type}` (placing the signature outside the computation for brevity), I need to be able to produce `[Err]{Type -> Type}`. That’s a tall order if `->` describes a real function arrow; but perhaps computation types give me a lever to reach it.

(Aside: what do Twelf & friends do? I’m given to understand that they are quite different, but I don’t know how to characterize those differences beyond “the function arrow is different.”)

_TBD: scoped effects._
