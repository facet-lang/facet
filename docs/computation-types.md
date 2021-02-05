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


## Facet

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


----


## Oct 23rd, 2020

CBPV separates value and computation types, with the slogan:

> A value _is_, a computation _does_.

Value types are ordinary data. Computations, curiously, include functions. It’s certainly reasonable that _calling_ a function yields a computation type, but that’s distinct—lambdas, the inhabitants of function types, are _themselves_ computations. Levy explained this in at least one of the presentations whose slides I read but I don’t remember the reasoning.

Regardless, values and computations are related via an adjunction between functors U and F. (F returns, U thunks—I think.) There are judgements for moving terms and types between the two spaces:

- `return`/`eval to` — `return` lifts a value to a computation; `eval to` evaluates a computation to a variable (and variables have value type). (`eval to` looks a little bit like a `let` binding. Levy writes it as `M to x.N`, which took me some time to figure out how to pronounce; “eval to” should be taken as pronunciation primarily and not an attempt to recast the actual connective.)
- `thunk`/`force` — `thunk` wraps a computation into a value; `force` runs a thunk in a computation.

`eval to` & `thunk` both take a computation to a value; dually, `return` & `force` both take a value to a computation. However, as these happen on opposite sides of the adjunction, they have quite different meanings.

```
    Γ ⊢v V : A
-------------------
Γ ⊢c return V : F A
```

```
Γ ⊢c M : F A     Γ, x : A ⊢c N : _B_
------------------------------------
     Γ ⊢c M eval to x . N : _B_
```

```
  Γ ⊢c M : _B_
----------------
Γ ⊢v thunk M : U _B_
```

```
  Γ ⊢v V : U _B_
------------------
Γ ⊢c force V : _B_
```

Importantly, these are all term-level judgements; none of these describe the type formers. There is no thunk type per se; rather, types are grouped into the computation types and the value types, rather like polarization does.


----


## Feb 5th, 2021

[Reading the slides from another of Levy’s presentations](https://www.cs.bham.ac.uk/~pbl/mgsfastlam.pdf), we see that fine-grain CBV’s value/computation divide can be seen as relating to the β and η laws for a given type. Since a value _is_, a term at value _type_ can’t perform effects, whereas a computation _returning_ a value might. Levy uses a set _E_ = {_CRASH_, _BANG_} of errors to illustrate the difference:

> a value Γ ⊢v V : A denotes a function ⟦V⟧ : ⟦Γ⟧ → ⟦A⟧
> a computation Γ ⊢c M : A denotes a function ⟦M⟧ : ⟦Γ⟧ → ⟦A⟧ + E

One can interpret the β and η laws in the pure lambda calculus as meaning “anything at type Bool is a boolean” (for one). But this fails to hold for computations: `error CRASH : Bool` no longer has this property, and is clearly not a value.

Facet’s value types include kinds like Type and Interface, (currently) built-in types like String, and user-defined datatypes. Values themselves, then, are inhabitants of these types, including e.g. fully-applied constructors. In fine-grain CBV values also include variables, but that’s less clear in Facet.

In Facet, we want functions to act on both values and computations—values for the usual meaning of function application, and computations for functions-as-handlers. Thus, it seems the context should hold variables of computation type. Consider:

```facet
try : { E, A : Type } -> [Error E] A -> [Error E] Either E A
{ [a] -> catch (inr a) inl }
```

Here, we want to forward a computation `a` along to `catch` for handling. This isn’t going to work if `a` is of value type, because any errors will have been thrown in the caller’s context, and `try` will never have the opportunity to catch them.

On the other hand, a regular handler (here focusing solely on `Throw`) paints a slightly different picture:

```facet
rethrow : { E, E' : Type } -> (f : E' -> E) -> [Throw E'] A -> [Throw E] A
{ [throw e ; _] -> throw (f e)
, a             -> a }
```
In the first clause, we only bind a single variable (`e`), of value type. In the second, again, `a` is a variable of value type: if there were effects other than `throw` in that position, they should have been issued/handled before control reaches this point.

As discussed above, computations embed values via `return`; values embed computations via `thunk` (in Facet, `{x}` is a 0-ary suspended computation). So the general solution is probably to place variables of computation type in the context and treat value patterns as automatically lifted over `return`s.

(Alternatively, the pattern `[a]` could bind a variable `a` of suspended computation type, requiring us to `!` (force) it to use it elsewhere. The two approaches are broadly equivalent, but it feels a bit strange to change the apparent type like that. On the other hand, it’s unfortunate that `a` claims to be able to perform effects!)
