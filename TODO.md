# TODO

_Caveat lector: there are no guarantees of correctness or completeness on the contents of this file._


## Language

### Core

- Substitution & renaming are specified manually over `Expr` & `Type`. This is brittle.

  It would be nice to abstract those operations one and for all; it would also be nice to test the hell out of them. Can we take advantage of the `Binding` traversal? It knows about binders after all…

- `let` bindings.

- Datatypes.

- Effects.

- Case expressions.

- Eliminate patterns in lambda domains.


### Surface

- `let` bindings.

- Datatypes.

- Effects.


## Components

### Elaborator

- Emit warnings.

- Continue after errors on a declaration-by-declaration basis.


### Pretty-printer

- Decompose into DSLs for printing parts of syntax, interpreters written against said DSLs, and composable implementations of the DSLs providing different behaviours for e.g. bound variable display.


### Driver

- Formatting.

- Running.

- Compilation.

- LSP.


### Tests

- Should exist 😅
