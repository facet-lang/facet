# TODO

_Caveat lector: there are no guarantees of correctness or completeness on the contents of this file._


## Architecture

- Now that we’ve got HOAS (more or less) under control, can we parse into it?

- Can we skip adding `Span` annotations to the AST and instead carry it around in a `Reader` by parsing and elaborating in a single context?

- Provide a more systematic treatment of types/expressions in (meta)context.

- LSP.

- Enriched intermediate languages for optimization.

- Definition-level incremental computation.
  - Definitional-level dependency tracking.

- Self-host.


## Language

### General

- Records.

- Some means to distinguish synonyms from definitions (structural vs. nominal typing).

  - Possibly `=`.


### Core

- `let` bindings.

- Computations.

- Effects.


### Surface

- `let` bindings.

- Effects.

- Group quantifiers of different kinds in a single set of braces.

- Allow binding operator names as local variables.

- Warn if binding a variable with the same name as an in-scope constructor in a pattern match? We can still write `true` when we mean to write `(true)` and be surprised at the results, it just can’t break out from under us.

- First-class documentation.

- First-class literate programming?


### Modules

- Imports.

- Submodules.

- Design the relationship between files and modules. Currently thinking of a file as a metalanguage “script” which _constructs_ a module.

  - Regardless, how does the compiler know where to find the file for any particular import? I want `:load` to load (transitive) dependencies; do we have to relate module names and file paths like `ghc`?

  - For that matter, how does the programmer know?

- Do we need to declare a module header with every file? Do we need to wrap the whole file in braces?

  - A header could be useful for stuff like language levels, versions, etc.

- How do we specify exports?

- Are modules “just” records?


## Components

### Parser

- Extend the precedence table for mixfix operators.


### Elaborator

- Emit warnings.

- Continue after errors on a declaration-by-declaration basis.


### Pretty-printer

- Preserve comments in surface syntax 😱

- Parenthesize operators occurring free in expressions.

- Can we deal with precedence in a more modular way, à la the approach the parser takes (cf https://ptival.github.io/2017/02/25/modular-parser-combinators/)?

- Increase the size of source excerpts so binding sites are visible; alternatively, have multiple excerpts when binding sites are far away.


### Driver

- Formatting.

- Running.

- Compilation.

- LSP.


### Tests

- Should exist 😅
