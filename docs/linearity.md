# Linearity

Conditionals are currently written something like so:

```facet
if
: { A : Type } -> (c : Bool) -> (t : {A}) -> (e : {A}) -> A
{ case c
  { (false) -> e!
  , (true)  -> t! } }
```

We can make stronger guarantees here with some sort of linear (or affine) annotations on the variables:

1. The type parameter `A` is operationally irrelevant and should be erased.

2. We use the condition exactly once.

3. We use the then branch at most once.

4. We use the else branch at most once.


Using a hypothetical syntax for such annotations, we might write:

```facet
if
: { erase A : Type } -> (linear c : Bool) -> (affine t : {A}) -> (affine e : {A}) -> A
{ case c
  { (false) -> e!
  , (true)  -> t! } }
```

but this misses an extra guarantee we would like to make:

5. We either use the then branch exactly once, or we use the else branch exactly once; never both.

(We can already see that we must use at least one of them by parametricity.) This corresponds to the linear multiplicative disjunction, ⅋; I don’t know how to express that cleanly in the types without changing the way one uses `if`.


## Polarity

### Products

There’s a notion of polarity that arises in linear logic; you can divide its terms into additive/multiplicative groups, or into negative/positive ones. Positive types are described primarily in terms of their constructors, whereas negative types are described primarily in terms of their eliminators. These are isomorphic in an unrestricted logical setting, but are quite distinct in a linear logic.

In particular, Noam Zeilberger relates these to a treatment of evaluation order. To set the stage, we can define positive & negative products in Haskell:

```haskell
data PPrd a b = PPrd a b -- essentially (a, b)

newtype NPrd a b = NPrd (forall r . (a -> b -> r) -> r)
```

In linear logic, the positive and negative conjunctions are written as ⊗ (multiplicative) and & (additive), respectively.

We can demonstrate their relationship to one another in an unrestricted setting simply by converting:

```haskell
prdPosToNeg :: PPrd a b -> NPrd a b
prdPosToNeg (PPrd a b) = NPrd (\ f -> f a b)

prdNegToPos :: NPrd a b -> PPrd a b
prdNegToPos (NPrd f) = f PPrd
```

Proof-theoretically (cf _[Polarity in Type Theory][]_, Bob Harper), we can view `PPrd a b` as a connective which allows us to prove whichever of `a` and `b` (or both) we wish directly; in that case, there’s no requirement that we evaluate the other yet (with obvious parallels to call-by-need/name). By contrast, the judgement for a `NPrd`–style connective (negative conjunction) states that a proof from the information contained within in `NPrd a b`, must have both `a` and `b` in its premise, which we can read as “evaluated” (call-by-value). Both kinds of conjunction—product—share the same introduction rule:

```
Γ ⊢ A true      Γ ⊢ B true
-------------------------- [conj-intro]
     Γ ⊢ (A ∧ B) true
```

Positive conjunction uses weakening to conclude both A true and B true (independently) from the stronger statement that both are true:

```
Γ ⊢ (A ∧ B) true
---------------- [pos-conj-elim-1]
   Γ ⊢ A true

Γ ⊢ (A ∧ B) true
---------------- [pos-conj-elim-2]
   Γ ⊢ B true
```

Negative conjunction instead has a single elimination rule:

```
Γ ⊢ (A ∧ B) true    Γ, A true, B true ⊢ C true
---------------------------------------------- [neg-conj-elim]
                  Γ ⊢ C true
```

Proving something from a negative conjunction requires that we prove the conjunction (as before), but additionally that we take the truth of both halves as assumptions for the proof of the conclusion. There’s no use of weakening, tho it surprises me a little that neither A nor B appears in the conclusion. (The type-theoretic presentation (i.e. involving explicit proof terms) Harper goes on to give shares this property.)


[Polarity in Type Theory]: https://existentialtype.wordpress.com/2012/08/25/polarity-in-type-theory/


### Sums

Sums can also be defined both negatively and positively:

```haskell
data PSum a b = PS1 a | PS2 b -- essentially Either a b

newtype NSum a b = NSum (forall r . (a -> r) -> (b -> r) -> r)
```

Here again, we can convert (in unrestricted Haskell):

```haskell
sumPosToNeg :: PSum a b -> NSum a b
sumPosToNeg (PS1 a) = NSum (\ f _g -> f a)
sumPosToNeg (PS2 b) = NSum (\ _f g -> g b)

sumNegToPos :: NSum a b -> PSum a b
sumNegToPos (NSum fg) = fg PS1 PS2
```

In linear logic, the positive and negative disjunctions are written as ⊕ (additive) and ⅋ (multiplicative), respectively.
