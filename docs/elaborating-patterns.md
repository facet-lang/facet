# Elaborating patterns

Some notes on elaboration of patterns. At a high level, I would like each `case` clause in core to extract the fields of a single constructor shallowly.


## Nested clauses

We should decompose sets of nested clauses into nested trees of lambdas and cases:

```facet
{ (true) (true) -> true
, _      _      -> false }
```

```facet-core
{ x -> case x of
  { (true) -> { y -> case y of
    { (true) -> true
    , _      -> false
    } }
  , _      -> false } }
```


## Nested patterns

We should decompose nested patterns in a single clause into nested shallow pattern matches.

```facet
{ (some (true)) -> true
, _             -> false }
```

```facet-core
{ x -> case x of
  { (some y) -> case y of
    { (true) -> true
    , _      -> false }
  , _ -> false } }
```
