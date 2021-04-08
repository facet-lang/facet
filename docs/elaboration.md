# Elaboration

Elaboration takes a syntactically valid surface program (resp. declaratio, definition, type, expression, etc) and either yields a semantically valid core program, or fails with an error (hopefully clear and informative enough to suggest a solution). The type language is simple enough that we’re going to ignore it for now and instead focus on the term language, which has some deviations from a standard bidirectional typechecker which warrant discussion.


## Syntax

The syntax is mostly unsurprising, featuring such diverse elements as contexts:

```
Γ ::= ◊ | Γ, x : τ | Γ, X : κ
```

Types:

```
τ ::= {X : κ} -> τ | X | τ -> τ
```


## Judgements

Elaboration occurs on both terms and types. The type level elaboration proceeds first, relating well-kinded surface types to core types. These core types are then used to inform the elaboration of terms. Note also that since Facet’s type system is quite simple, we enjoy an entirely inferred kinding judgement.

Elaboration of terms is _specified_ as a single judgement relating surface terms to core terms at a core type. However, it is _performed_ bidrectionally, and thus in practice consists of two judgements, checking and synthesis. We’ll give rules for each of these as convenience allows.


### Typing

```
Γ ⊢ S ~~> T ==> K
```

This judgement describes the elaboration of surface types `S` to core types `T` with synthesized kinds `K`. (The kind language is particularly simple, consisting of the base kinds `Type` and `Interface`, and arrow kinds.)

Note that the same symbols this judgement employs are also used by the term-level synthesis judgement, below. The term and type languages are disjoint, so we are free to overload the symbols without ambiguity (if not _necessarily_ without confusion).

As described above, our kinds are quite simple, so we can elaborate types entirely in synthesis mode. However, it is nevertheless convenient in the implementation to operate bidirectionally in the small, by synthesizing a type’s kind and then immediately checking it against our expectation using the ubiquitous switch rule. For that reason, we can also reference type elaboration in checking mode in premises:

```
Γ ⊢ S ~~> T <== K
```

with the understanding that proof search will immediately switch (as this is the only checking-mode conclusion in the type elaboration judgement) and check the kinds for equality:

```
Γ ⊢ S ~~> T ==> K′   K ≡ K′
---------------------------
     Γ ⊢ S ~~> T <== K
```

(where equality of kinds is syntactic.)


### Elaboration

```
Γ ⊢ M ~~> V : τ
```

This judgement can be recovered by “erasing” the directionality of the two bidirectional judgements by replacing the `<==`/`==>` symbols with `:`. Note that this judgement is in general nondeterministic, and thus should not be considered as specifying an algorithm. (That’s what the bidirectional judgements are for.)


### Checking

```
Γ ⊢ M ~~> V <== τ
```

This judgement is used to elaborate syntax where we need to know the type in advance.


### Synthesis

```
Γ ⊢ M ~~> V ==> τ
```

This judgement is used to elaborate syntax where we can deduce the type from the term itselr, perhaps requiring that we are able to deduce some or all of it from its components.


### Syntax- vs. type-directed

Bidirectional typecheckers are typically _syntax-directed_, meaning that we can typecheck by walking over the input syntax and alternately checking/synthesizing according to what piece of syntax we’re looking at. This has the nice property that there are no _choices_, i.e. no points at which there might be two ways to arrive at a result, each of which could fail independent of the other, and which would therefore require wasteful backtracking.

In Facet’s case, matters are muddied slightly by computations, which are not explicit in the surface syntax for terms, but are instead indicated by the type. That is, a term at type `A` may well elaborate differently than the same syntactic term at type `[…] A`. Note that I’m saying `[…] A`, which embeds `A`, and not (for example) some unrelated type `B`; the distinction is solely on the presence or absence of a computation type around the result type.


### Computation types

Computation types are computations in the CBPV/polarization sense, i.e. negative, and thus are lazily evaluated. The elaborator models this by treating them as a kind of function type mapping products of operations—dictionaries—to the computed result.


## Strategy

Computation types arise in arguments and returns.


### Positive terms

Facet’s implementation isn’t currently polarized, but it’s a good model for thinking about the structure of the system. (The primary difference in the implementation is that we don’t distinguish thunk types; nullary computations are instead encoded as functions from unit.)


#### String literals

```
--------------------------
Γ ⊢ "…" ~~> "…" ==> String
```


#### Thunks

Technically these can’t appear in the surface syntax right now, but here’s the proposed rule. (It bidirectionalizes trivially by replacing `:` with `<==`/`==>` in both premise and conclusion.)

```
     Γ ⊢ M ~~> M′ : T
--------------------------
Γ ⊢ {M} ~~> {M′} : Thunk T
```

Thunks are eliminated by forcing:

```
Γ ⊢ M ~~> M′ : Thunk T
----------------------
  Γ ⊢ M! ~~> M′! : T
```


### Negative terms

#### Functions

Functions are defined using curly braces containing pattern matching clauses. These define not only functions in the typical sense, but also effect handlers, making them (paraphrasing the Frank paper, _Do Be Do Be Do_) a more general sort of coroutining construct. Here’s the pure case (functions without effect handlers), ignoring (for the moment) non-variable patterns, nested lambdas, and multiple clauses:

```
        Γ, x : S ⊢ M ~~> M′ <== T
-----------------------------------------
Γ ⊢ { x -> M } ~~> { x -> M′ } <== S -> T
```

Pure applications, likewise, just distribute the elaboration of the terms while synthesizing the type:

```
Γ ⊢ M ~~> M′ ==> S -> T   Γ ⊢ N ~~> N′ <== S
--------------------------------------------
          Γ ⊢ M N ~~> M′ N′ ==> T
```


### Computations

Things get more interesting once we start talking about arguments and returns at computation types. The critical observation for the elaboration of computations is that a computation type `[σ̅] T` intuitively represents a promise to produce `T`s given facilities for the operations in `σ̅`. Further decomposing that, we have “a promise to produce `T` given _something_,” and “facilities for the operations in `σ̅`.” We already have a connective for producing `T` given _something_: `something -> T` represents precisely such a promise. And for the latter component, we can represent the facilities for an effect’s operations by a dictionary of the operations’ implementations, as provided by a handler.

Thus, we elaborate computation _types_ into functions from dictionaries of effect handlers to the return type:

```
Γ ⊢ σ̅ ~~> σ̅′ <== Interface   Γ ⊢ T ~~> T′ <== Type
--------------------------------------------------
        Γ ⊢ [σ̅] T ~~> [σ̅′] -> T′ ==> Type
```

where `[σ̅]` (to the right of the `~~>`) can now be understood as an n-ary type constructor named `[]` taking zero or more interfaces to a type. (We do not show a type formation rule for this type since it cannot appear in the surface syntax except composed into a computation type, which is already covered by the elaboration judgements.)

The meat of this approach centres on terms. Unlike other types, terms at computation type:

1. have (almost) no corresponding explicit term-level syntax;
2. implicitly embed positive terms by returning them à la CBPV; and
3. propagate part of the context into (some) subterms

The first point means that we can no longer elaborate with a purely syntax-directed algorithm, because the syntax alone doesn’t suffice to determine what sort of term should be output. Instead, a string literal elaborated at `[σ̅] String` should first be elaborated as a `String` before being lifted into the computation via a return; this is an example of the second point in action.

The third point is subtler. Consider the expression `incr ; incr`, where `incr` increments a mutable variable and returns the new value, and `;` is the definition in `Data.Function`. The type of `incr` is `[State Int] Int`, which we elaborate to `[State Int] -> Int`:

```facet
(incr : [State Int] -> Int) ; (incr : [State Int] -> Int)
```

Whereas before the operands to `;` were computations, now they are functions. The type of `;` (`_ ; _ : {A, B : Type} -> A -> B -> B`) is polymorphic and will accommodate them, but returning a function does not have the same semantics as running a computation. We need to arrange for the correct dictionary to be passed in.

Note that since the type of `;` indicates that it returns the result of its second argument, not its first; thus, we could apply only the result of the expression to the dictionary. However, this would not work for many other operations, and would still not have the desired semantics, since we expect the original expression to increment the variable _twice_.

Thus, despite the fact that the arguments to `incr` are occurring in positions not obviously of computation type, we are obligated to arrange for them to nevertheless receive the relevant dictionaries. The elaborated term should therefore be:

```facet
(incr : [State Int] -> Int) dict ; (incr : [State Int] -> Int) dict
```

where `dict` is the name bound in the context for the `[State Int]` dictionary. Thus, elaboration has to resolve computation types not just at e.g. return positions in lambdas, but within applications therein.

Furthermore, we also need to know where the dictionary came into scope. Zooming out from the single expression, we’ll define a top-level term `incr2`:

```facet
incr2 : [State Int] Int
{ incr ; incr }
```

Since `incr2` is typed as `[State Int] Int`, we can see that its elaboration will have type `[State Int] -> Int`. Thus, instead of the body being an application, it must now be a lambda binding the dictionary:

```facet
incr2 : [State Int] -> Int
{ [get, put] -> … }
```

Here we see a slight discrepancy with the above: the dictionary is fully decomposed into its operations. Thus, when elaborating the body, we’ll need to reconstruct the dictionary to give to child terms. (This allows them to receive only the operations they require, which might be quite a small subset of the available terms, rather than the dictionary for all available effects.) In full, we now have:

```facet
incr2 : [State Int] -> Int
{ [get, put] -> incr [get = get, put = put] ; incr [get = get, put = put] }
```

where the `[x̅ = y̅]` notation in the body is a record (in this case, a dictionary) giving field `x` the value `y`.
