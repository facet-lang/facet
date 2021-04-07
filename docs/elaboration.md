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

Elaboration is performed bidrectionally, and thus consists of two judgements, checking and synthesis.


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
