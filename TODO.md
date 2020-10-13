# TODO

_Caveat lector: there are no guarantees of correctness or completeness on the contents of this file._


## Architecture

- Now that we’ve got HOAS (more or less) under control, can we parse into it?

- Can we skip adding `Span` annotations to the AST and instead carry it around in a `Reader` by parsing and elaborating in a single context?

- Provide a more systematic treatment of types/expressions in (meta)context.


## Language

### Core

- Substitution & renaming are specified manually over `Expr` & `Type`. This is brittle.

  It would be nice to abstract those operations one and for all; it would also be nice to test the hell out of them. Can we take advantage of the `Binding` traversal? It knows about binders after all…

- `let` bindings.

- Datatypes.

- Effects.

- Case expressions.

- Eliminate patterns in lambda domains.

- Type application expressions.


### Surface

- `let` bindings.

- Datatypes.

- Effects.

- Allow binding operator names as local variables.


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

- Insert type application expressions for quantifiers.

  These will presumably have to be metavariables, so we’ll further need to solve for them. Substitution presents its bill at last.


### Pretty-printer

- Decompose into DSLs for printing parts of syntax, interpreters written against said DSLs, and composable implementations of the DSLs providing different behaviours for e.g. bound variable display.

- Disincline the printer to format declarations on a single line.

- Space out declarations in module bodies better.

- Preserve comments in surface syntax 😱

- Parenthesize operators occurring free in expressions.

- Can we deal with precedence in a more modular way, à la the approach the parser takes (cf https://ptival.github.io/2017/02/25/modular-parser-combinators/)?

- Rainbow highlighting of local variables introductions & references. Including in error contexts!

- Increase the size of source excerpts so binding sites are visible; alternatively, have multiple excerpts when binding sites are far away.


### Evaluator

- Should exist 😅



### Driver

- Formatting.

- Running.

- Compilation.

- LSP.


### Tests

- Should exist 😅
