# Facet: a call-by-value functional language with algebraic effects, runners, quantitative type theory, and phasing

## Features

- 📈 functional programming!
- ✋🏻 strict (call-by-value) evaluation order
- 👷🏻‍♀️ algebraic effects
- ℹ️ (currently) embedded in Haskell as a (typed) EDSL


## Goals

- effects as sole mechanism for ad hoc polymorphism; arithmetic, comparison, etc., performed via effects (thus, can be overridden locally)
  - some system for (ideally coherent) defaulting
- quantitative type theory controlling phasing and erasure in particular
  - specialization & inlining of handlers
- compilation
  - fine-grained incremental compilation
- metaprogramming & general elaborator reflection via effects
- syntax desugaring via effects
- data representation as an effect; peano numerals & nat-as-int should be interconvertable
- elaboration, optimization, & compilation reflected via an effectful DSL


## Non-goals

- elision of signature variables; I’m willing to be completely explicit (for now at least)


## Development

Make sure you have a recent enough `ghc` (8.10+) and `cabal` (3+); I’m not testing against older versions. On macOS, I recommend `ghcup`.

I do just about everything via `ghci`, which can be conveniently initialized and launched as follows:

```
cabal build # make sure dependencies are known & installed
script/repl # actually launch the repl
```

`ghcide` integration is also provided, and I edit in VS Code configured to use it.


## TODO

- concrete syntax
  - pretty-printer
  - parser
- driver executable
