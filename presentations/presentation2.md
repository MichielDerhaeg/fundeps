Title
=====

**Implementation of Type Inference and Elaboration in System Fc for Functional Dependencies**

Functional Dependencies
=======================

```haskell
class Collection c e | c -> e where
    singleton :: e -> c

instance Collection [a] a where
    singleton x = [x]

singleton2 :: (Collection c1 e, Collection c2 c1) => e -> c2
singleton2 c = singleton (singleton c)
```

First slide without functional dependency.

Type classes are used to implement traits of types, TC's with multiple
parameters for relationships between types.

``singleton2`` will be rejected because ``c1`` does not appear in the rhs of the
type signature and is therefore ambiguous even if there is only one possible
instance to choose from. Because this can change when more instances are added.
Making an arbitrary choice from the available instances might might result in a
well typed program, but the implementation can arbitrarily change as well and we
therefore disallow these ambiguous programs.

Adding the functional dependency means that there can be only one ``e`` for
every ``c`` and we enforce that there can be only one instance to choose from.

So this is now disallowed:
```haskell
instance Collection ByteArray Byte
instance Collection ByteArray Bit
```

So now if we know ``c2``, we can derive ``c1`` because it is uniquely determined
by ``c2`` and no longer ambiguous because it's enforced that there is only one
option.

Problem Statement
=================

```haskell
class C a b | a -> b
instance C Int Bool

f :: C Int b => b -> Bool
f x = x
```

``b`` is clearly ``Bool``, but GHC currently rejects this because the
relationship between ``Int`` and ``Bool`` cannot be translated into System F, an
intermediate representation used by many functional language implementations.

Solution
========

*Elaboration on Functional Dependencies*,
George Karachalias, Tom Schrijvers, 2017
  * Implement type inference
  * Use type equality coercions in elaboration

Goals
=====

  * Part 1: Implementation of
    - Type Inference
    - Elaboration into System Fc
    - GADTs and Type Families

  * Part 2: Interaction of all features

Plan & State
============

  * Gert-Jan's implementation of Quantified Class Constraints
  * Simplify to Haskell '98
  * Extend with:
    - System Fc *mark as done til here*
    - Dormant type equalities
  * Implement algorithm from *Elaboration on Functional Dependencies*
  * Implement Type Families and GADTs

Challenges
==========

  * Superclasses without backtracking

```haskell
class Eq a
class Eq a => Ord a

instance Eq a => Eq [a]

sort :: Ord a => [a] -> [a]
```

Superclass constraint implications match in the other direction because having
``Ord a`` implies we have ``Eq a``.

E.g. we need to solve ``Eq [a]``, through matching the rules in the wrong order
we end up with ``Ord [a]`` as a constraint to be solved, which we can't.
Calculate transitive superclasses when adding local given constraints.

  * Extending System F with Type Equality Coercions

```haskell
λa:t. e                 -- simply typed lambda calculus
Λt. λa:t. e             -- System F
Λt1. Λc:t1~t2. λa:t1. e -- System Fc
```
System F provides explicit type parameters which enables parametric
polymorphism.  Fc includes another kind of parameter: type equality coercions.
``c`` is a proof that type ``t1`` equals ``t2``. Which means we can use ``c`` to
explicitly cast an expression of type ``t1`` to ``t2``. The Fc typechecker
computes if ``c`` indeed implies ``t1~t2``.

Explain that having a new type of variable broke existing abstractions for local
environments which had to be replaced entirely.

I could show a solution for ``f :: C Int b => b -> Bool``.
```
type FD a
axiom a1 : FC Int ~ Bool
f = Λb. λx:b. x
```

Possible Future Challenges
==========================

  * No existing literature on how to make sure the new type inference algorithm
    doesn't loop indefinitely. But it has been done before. (in GHC)

  * The dormant equality constraints in the Haskell typechecker will break a lot
    of abstractions, no clear seperation between solving and generating
    constraints like in HM.

Related work
============

  * Types and Programming Languages
  * OutsideIn(X)
  * System F with Type Equality Coercions
  * Elaboration on Functional Dependencies
  * Quantified Class Constraints
  * How to make *ad-hoc* polymorphism less *ad hoc*

[Powerpoint link](https://seafile.derhaeg.be/f/416a34ab2d9b4efba599/)

Notes
=====
make slide about elaboration/ir koen style
more explicit problem statement
example for non-termination?
