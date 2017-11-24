Title
=====

**Implementation of Type Inference and Elaboration in System Fc for Functional
Dependencies**

Functional Dependencies
=======================

```haskell
class Collection c e | c -> e where
    singleton :: e -> c

instance Collection [a] a where
    singleton x = [x]

singleton2 :: (Collection c1 e, Collection c2 c1 ) => e -> c2
singleton2 c = singleton (singleton c)
```

First slide without functional dependency.

Type classes are used to implement traits of types, TC's with multiple
parameters for relationships between types.

``singleton2`` will be rejected because ``c1`` does not appear in the rhs of the
type signature and is therefore ambiguous.

Adding the functional dependency means that there can be only one ``e`` for
every ``c``.

So this is now disallowed:
```haskell
instance Collection ByteArray Byte
instance Collection ByteArray Bit
```

So now if we know ``c2``, we can derive ``c1`` and it's no longer ambiguous
because it's enforced that there is only one option and it'll compile just fine.

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

  * Part 1
    - Implementation of type inference
    - elaboration into system fc
    - GADTs and Type Families

  * Part 2
    - Interaction of all features

Plan & State
============

  * GJ's QCC implementation
  * Haskell '98
  * Extend with:
    - System Fc *mark as done til here*
    - Dormant type equalities
  * Implement paper algorithm
  * Implement TF's & GADTs

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

I could show a solution for ``f :: C Int b -> b -> Bool``.

Possible Future Challenges
==========================

  * No existing literature on how to make sure the new type inference algorithm
    doesn't loop indefinitely. But it has been done before. (in GHC)

  * The dormant equality constraints in the Haskell typechecker will break a lot
    of abstractions, no clear seperation between solving and generating
    constraints like in HM.

Related work
============

  * TAPL
  * OutsideIn(X)
  * System Fc paper
  * FD's paper
  * QCC paper
  * ad-hoc polymorphism less ad hoc paper
