# Facet: a call-by-value functional language with algebraic effects, quantitative type theory, and staging

_Caveat lector:_ facet is quite new, and this document is primarily aspirational. Many things do not work, are not implemented, or are poorly thought-out.


## Features

- 📈 functional programming!
- ✋🏻 strict (call-by-value) evaluation order
- 👷🏻‍♀️ algebraic effects


## Goals

- effects as sole mechanism for ad hoc polymorphism; arithmetic, comparison, etc., performed via effects (thus, can be overridden locally)
  - some system for (ideally coherent) defaulting
- quantitative type theory controlling staging and erasure in particular
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

`haskell-language-server` integration is also provided, and I edit in VS Code configured to use it.


## Syntax

A quick overview of facet’s syntax. Note that this is subject to change.


### Comments

Line comments start with `#`. There are no block comments.

```facet
# comments are like this
```


### Declarations

Declarations live at the top level of a file, and have a name, a signature, and a body wrapped in braces.

```facet
unit1 : Unit
{ unit }
```

A declaration’s signature gives its type, and can also bind variables. Variables bound in the signature are in-scope in the body.

```facet
id1 : (x : Unit) -> Unit
{ x }
```


### Functions

If we didn’t bind the variable in the signature, we could instead bind it by pattern matching in the body. Function bodies range over any variables unbound in the signature. For example, the above definition of `id1` is equivalent to:

```facet
id2 : Unit -> Unit
{ x -> x }
```

Functions are typically defined in _curried_ style: a function of two arguments is a function of one argument whose result is a function of one argument. Multiple variables can be bound either in the signature:

```facet
const1 : (a : Unit) -> (b : Unit) -> Unit
{ a }
```

the body:

```facet
const2 : Unit -> Unit -> Unit
{ a b -> a }
```

or a mixture:

```facet
const3 : (a : Unit) -> Unit -> Unit
{ b -> a }
```

Unused parameters can be ignored with a _wildcard_ pattern, written as `_`, whether in the signature:

```facet
const4 : (a : Unit) -> (_ : Unit) -> Unit
{ a }
```

or the body:

```facet
const5 : Unit -> Unit -> Unit
{ a _ -> a }
```

From here on, we’ll prefer to bind variables in the signature rather than the body.


### Types

Functions can have type parameters, which are bound in the signature like term variables, but written in initial caps and wrapped in curly braces instead of parentheses:

```facet
id3 : { A : Type } -> (a : A) -> A
{ a }
```

Type variables are in scope in the rest of the signature, and in the body. Unlike parameters, they cannot be bound in the body, only in the signature. There is no implicit generalization of free type variables in the signature (or elsewhere); free type are assumed to be globals, and will error if they’re not in scope.

Multiple type variables of the same kind can be bound separately:

```facet
const6 : { A : Type } -> { B : Type } -> (a : A) -> (b : B) -> A
{ a }
```

or can be combined into a single set of braces:

```facet
const7 : { A, B : Type } -> (a : A) -> (b : B) -> A
{ a }
```


### Data

Data types are defined using a similar syntax to other declarations, but with init-caps names (like all Facet types). The block contains a comma-separated list of zero or more _constructors_, with init-lowercase names (like all Facet terms) followed by their types. For example, here is how you would define a boolean type (if one weren’t already defined for you):

```facet
Bool : Type
{ false : Bool
, true  : Bool
}
```

Constructors with fields include them in their types:

```facet
BoolPair : Type
{ boolPair : Bool -> Bool -> BoolPair
}
```


### Patterns

Values can be examined and destructured by means of pattern matching. Function arguments—in curly braces, to the left of the arrow—are matched with patterns. The simplest case is a variable:

```facet
id : { A : Type } -> A -> A
{ x -> x }
```

If you don’t need to use the argument, you can also use a _wildcard_, written as an underscore (`_`), to ignore it:

```facet
const : { A, B : Type } -> A -> B -> A
{ a _ -> a }
```

Data constructors, introduced by datatypes, can be matched by mentioning their names (and further patterns for any fields) within parentheses; multiple pattern-matching _clauses_ are separated by commas:

```facet
not : Bool -> Bool
{ (false) -> true
, (true)  -> false
}
```

(Requiring parentheses around constructor patterns allows us to distinguish them from variable patterns, and thus to avoid accidentally introducing bugs when a constructor is renamed or typo’d.)

Patterns are matched in top-down order; the first matching clause will be executed. It is an error for no patterns to match.

_TBD: exhaustiveness; tuples; effect constructors_


### Effects


### Handlers
