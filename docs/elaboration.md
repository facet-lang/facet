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
