# TODO

_Caveat lector: there are no guarantees of correctness or completeness on the contents of this file._


## Core

- Substitution & renaming are specified manually over `Expr` & `Type`. This is brittle.

  It would be nice to abstract those operations one and for all; it would also be nice to test the hell out of them. Can we take advantage of the `Binding` traversal? It knows about binders after all…


## Tests

- Should exist 😅
