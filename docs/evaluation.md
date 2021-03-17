# Evaluation relation in sequent calculus

This is a presentation of Facet’s evaluation rules in sequent calculus. The evaluation relation `⤋` (I’m using this character because it draws bigger and is easier to distinguish than `⇓` in my editor font) can be thought of as being typed something like so:

```
Env [Sig] ⊢ Expr ⤋ Value  --  eval
```

or … tupled? I guess? like so:

```
_ [_] |- _ ⤋ _ : (Env, Sig, Expr, Value) s.t. (Env, Sig, Expr) -> Value
```


A couple of notes to begin:

1. The presentation is not extremely polished, it’s more of a tool for organizing my thoughts while working on it than a rigourous specification.

2. There are two environments, one (`Γ`) carries values and the other (`Σ`) holds effect handlers.

3. Some rules are presented in a couple of different ways. In some cases this is intended to indicate that if we were to have a normal form which evaluates under binders à la normalization by evaluation, then it might slot in there. In other cases they’re just derived applications of more general rules to specific cases (e.g. lambdas which don’t handle effects).

4. There are actually two relations, `⤋₋` and `⤋₊`, because this was written on a branch where I had polarized types and terms. That polarization is not currently maintained in the Haskell implementation of the syntax, but is still (mostly) morally valid; but the actual `eval` function is not polarized.

5. There are rules for thunks and forcing, which don’t actually exist in the language. We instead model them with functions from unit and application to unit, which hints at the most notable deviation from CBPV/a polarized calculus, which is that we don’t distinguish between functions and their thunks the way CBPV does.


```
-------------------   eval string
Γ [Σ] ⊢ "…" ⤋₊ "…"
```

```
---------------------------   eval thunk
Γ [Σ] ⊢ thunk c ⤋₊ thunk c
```

```
      Γ [Σ] ⊢ c ⤋₋ c′
---------------------------   eval thunk (alternate)
Γ [Σ] ⊢ thunk c ⤋₊ thunk c′
```

```
---------------------------------   eval lambda, pure
Γ [Σ] ⊢ { x -> y } ⤋₋ { x -> y }
```

```
------------------------------------------   eval lambda, pure, decomposed
Γ [Σ] ⊢ { xᵢ -> yᵢ, … } ⤋₋ { ∑ᵢ xᵢ -> yᵢ }
```

```
-----------------------------------------------------   eval lambda
Γ [Σ] ⊢ { x -> y, [e] -> z } ⤋₋ { x -> y, [e] -> z }
```

```
       Γ, x [Σ] ⊢ y ⤋₋ y′
----------------------------------   eval lambda, pure (alternate)
Γ [Σ] ⊢ { x -> y } ⤋₋ { x -> y′ }
```


```
     Γ [Σ] ⊢ y ⤋₋ y′
---------------------------   eval type lambda
Γ [Σ] ⊢ { {X} -> y } ⤋₋ y′
```

```
  Γ [Σ] ⊢ f ⤋ f′
-------------------   eval type application
Γ [Σ] ⊢ f {X} ⤋₋ f′
```


```
       Γ [Σ] ⊢ v ⤋₊ v′
-----------------------------   eval return
Γ [Σ] ⊢ return v ⤋₋ return v′
```


```
Γ [Σ] ⊢ v ⤋₊ thunk c   Γ [Σ] ⊢ c ⤋₋ c′
---------------------------------------   eval force
        Γ [Σ] ⊢ force v ⤋₋ c′
```


```
   Γ ∋ x = v
---------------   eval variable
Γ [Σ] ⊢ x ⤋₊ v
```

```
Γ [Σ] ⊢ f ⤋₋ { x -> y }   Γ [Σ] ⊢ a ⤋₊ a′   Γ, x = a′ [Σ] ⊢ y ⤋₋ y′
--------------------------------------------------------------------   eval application, pure
                         Γ [Σ] ⊢ f a ⤋₋ y′
```

```
Γ [Σ] ⊢ f ⤋₋ { x -> y, [e] -> z }   Γ [Σ, [e] -> z] ⊢ a ⤋₊ a′   Γ, x = a′ [Σ] ⊢ y ⤋₋ y′
----------------------------------------------------------------------------------------   eval application, effectful
                                  Γ [Σ] ⊢ f a ⤋₋ y′
```


```
Σ ∋ [op y̅] -> c   Γ, y̅ = x̅ [Σ] ⊢ c ⤋ c′
---------------------------------------   eval operation (CPS should be straightforward)
          Γ [Σ] ⊢ op x̅ ⤋₋ c′
```

(famous last words here)
