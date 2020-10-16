# syntax

```
map
: (f : a -> b) -> List a -> List b
{ (nil)       -> nil
, (cons x xs) -> cons (f x) (map f xs)
}

(;) : (_ : b) -> (a : a) -> a
{ a }


List : (a : Type) -> Type # NB: implicit Mu here
{ nil  : List a
, cons : a -> List a -> List a
}

Void : Type
{}

absurd : Void -> a
{}

Bool : Type
{ false : Bool
, true  : Bool
}

not : Bool -> Bool
{ (false) -> true
, (true)  -> false
}

And : (a : Type) -> (b : Type) -> Type
{ and : a -> b -> And a b }

Or : (a : Type) -> (b : Type) -> Type
{ orL : a -> Or a b
, orR : b -> Or a b
}

# Abort : (a : Type) -> Interface
# { aborting : Void }
#
# abort : [Abort]a
# { case aborting! {} }

Abort : (a : Type) -> Interface
{ abort : a }

Option : (a : Type) -> Type # kinda seems like this should be derivable from Abort
{ none :      Option a
, some : a -> Option a
}

# an Implementation is a well-known handler
Abort : { a : Type } -> Implementation (Abort (Option a)) # give it a name so we can export it I guess
{ x            -> some x
, <abort -> k> -> none
}



Map : (f : Type -> Type) -> Interface
{ map  : (a -> b) -> f a -> f b
, (<$) :       b  -> f a -> f b
  { b fa = const b <$> fa } # default definition; there is no notion of default signatures thus far
}
Map : (f : Type -> Type) -> Interface
{ map  : (a -> b) -> f a -> f b
, (<$) :       b  -> f a -> f b
, (<$) :  (x : b) -> f a -> f b
  { map (const x) } # default definition with a second type signature binding variables and potentially requiring constraints
  # no reason we couldn’t have multiple such tho I don’t want to think about what the algorithm for selecting a path to a valid implementation should look like if e.g. both work; and I don’t really want to require that my constraint solver do backtracking
}

# ad hoc polymorphism; technically the same machinery as effects underneath, but you can overload it locally
# if you’re good with ruining coherence for everybody, I mean
Map : (f : Type -> Type) -> Implementation # this has to be typechecked as an open definition… somehow
{ Option -> # here we’re reusing the usual lambda syntax for a Λ-abstraction, “pattern matching” (perhaps literally?) on the type constructor
  { map : (f : a -> b) -> Option a -> Option b # giving the type again allows us to bind variables, otherwise we’d have to do something like (<$>) = { f none -> …, f (some a) -> … }
    { (none)   -> none
    , (some a) -> some (f a)
    }
  }
}
# can we express interfaces with closed implementations? does that even make any sense with local overrides?
# can we prevent local overrides? can we say “oh hey this is a global implementation so we’re gonna enforce coherence” instead?

Map : Implementation (Map Option) # this has to be typechecked as an open definition… somehow
{ map : (f : a -> b) -> Option a -> Option b # giving the type again allows us to bind variables, otherwise we’d have to do something like (<$>) = { f none -> …, f (some a) -> … }
  { none   -> none
  , some a -> some (f a)
  }
}

Implementation : { a, b : Type } -> (i : Interface) -> (handle : <i>a -> b) -> ?? some opaque thing maybe?
{ … ?? }

Map : Implementation (Map Option)
{ <map f o -> k> -> case o
  { (none)   -> none
  , (some a) -> k (f a)
  }
}

Map : Implementation (Map Option)
{ <map _ none     -> _> -> none
, <map f (some a) -> k> -> k (f a)
}


Eq : (A : Type) -> Interface
{ (==) : A -> A -> Bool }

(/=) : {A : Type} -> (a : A) -> (b : A) -> [Eq A]Bool
{ not (a == b) }


Semigroup : (A : Type) -> Interface
{ (<>) : A -> A -> A }

Monoid : (A : Type) -> [Semigroup A]Interface
{ zero : A }

Semiring : (A : Type) -> [Semigroup A]Interface
{ (><) : A -> A -> A }

Unital : (A : Type) -> [Semiring A, Monoid A]Interface
{ one : A }




if
: { A : Type } -> (c : Bool) -> (t : {A}) -> (e : {A}) -> A
{ case c { (true) -> t! , (false) -> e! } }

bool
: { A : Type } -> (e : {A}) -> (t : {A}) -> Bool -> A
{ (false) -> e!
, (true)  -> t!
}




# data Expr
# { lam : (Expr a -> Expr b) -> Expr (a -> b)
# | _ $ _ : Expr (a -> b) -> Expr a -> Expr b
# }



Reader : (r : Type) -> Interface
{ ask : r
, local : (r -> r) -> {a} -> a
}

runReader : (a : r) -> [Reader r]a -> a
{ x                -> x
, <ask       -> k> -> runReader r (k a)
, <local f m -> k> -> runReader r (k (runReader (f r) m))
}





withSucc
: (m : Unit -> a) -> [Reader Nat]a
{ local succ m }
```



----


- well-formedness or w/e of contexts, types, terms, signatures
- “if Γ ⊢ P, then Γ,x : τ ⊢ P subject to the restriction that x ∉ fvs(P)

- fvs of a term
-


# initial context might be the global env
τ(env) # types
  := Type                                  # might appear in kind signatures for example. no stratification (for now); impredicativity
  |  tvar s.t. tvar ∈ env                  # in-scope type variables; _no_ implicit binding/generalization of type variables
  |  τ(env) -> τ(env)                      # function types over scope-safe types
  |  { tvar : τ(env) } -> τ(env ∪ {tvar})  # forall, binding a type variable. NB: we don’t handle shadowing here because this definition is recognition, not resolution

σ := [] | (ε, σ) # effect signatures

ε := … # effects


idea:
- types include computations under some signature σ producing a value of type τ: σ{τ} (should τ itself include computations? maybe not?)
- when


# context judgements


# type judgements

---------------
Γ ⊢ Type : Type    # 🕶 deal with it


# typing judgements

- these should really be split up into synthesis & checking forms to be more algorithmic?

Γ ⊢ f : α -> τ    Γ ⊢ x : α
----------------------------   [ bog-standard app ]
        Γ ⊢ f x : τ


-- this first premise is wrong I think
Γ ⊢ x : α      Γ, x : α ⊢ y : τ
-------------------------------   [ bog-standard lam ]
    Γ ⊢ { x -> y } : α -> τ



Γ ⊢ f : (σ,F)α -> (σ)τ    Γ ⊢ x : (σ,F)α
----------------------------------------
            Γ ⊢ f x : (σ)τ

Γ ⊢ f : (σʹ)α -> (σ)τ    Γ ⊢ x : (σʹ)α   Γ ⊢ σʹ ⊂ σ
---------------------------------------------------  [ generalization of the above to handle any subset of the signature; this is probably not really ok ]
                  Γ ⊢ f x : (σ)τ

Γ ⊢ (σ,F)x : α     Γ, x : α ⊢ y : τ
-----------------------------------
  Γ ⊢ { x -> y } : (σ,F)α -> (σ)τ



Γ ⊢ f : (σ,F)α -> (σ)τ    Γ ⊢ x : (σ,F)α
----------------------------------------
            Γ ⊢ f x : (σ)τ

Γ ⊢ (σ,F)x : α      Γ, x : α ⊢ y : τ
-------------------------------
    Γ ⊢ { x -> y } : (σ,F)α -> (σ)τ



Γ ⊢ (σ,ε)τ
----------    [pure]
 Γ ⊢ (σ)τ



# signature judgements

----------   # empty signatures are valid
Γ ⊢ [] sig



Γ ⊢ l sig   Γ ⊢ r sig
---------------------   # we should probably do something syntactic here to indicate that signatures are notionally flat sequences and that we can decompose them any-old-how so long as we’re consistent about ordering — i.e. associative but not commutative
   Γ ⊢ [l, r] sig


Γ ⊢ i : Interface
---------------  # for now just pretending they’re binary trees and that these judgements make sense as is
 Γ ⊢ [i] sig



# interface judgements

Γ ⊢ i : Interface # honestly this might be fine


----

```
Base : Module
{ Bool : Module { import Base.Bool }
, List : Module
  { import Base.List }
}

Base.Bool : Module
{ Bool : Type
  { false : Bool
  , true  : Bool
  }

  not : Bool -> Bool
  { (false) -> true
  , (true)  -> false
  }

  bool
  : (e : {a}) -> (t : {a}) -> Bool -> a
  { (false) -> e!
  , (true)  -> t!
  }

  if
  : (c : Bool) -> (t : {a}) -> (e : {a}) -> a
  { case c { (true) -> t! , (false) -> e! } }
}
```


## open questions

should we generalize binding variables in signatures to pattern matching?
