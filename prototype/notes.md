Notes
=====

  * Fontend/HsTypes.hs:ftDropSuper puts local schemes first, they need to be
    prioritised because of super classes, don't forget to mention this.
    - Will become irrelevant anyway

  * Data constructor environment info carries polytypes instead of monotypes
    because the tycon and datacon info is translated and carried over into
    system fc and dictionary data constructors would have polytypes in haskell
    which is rather dirty. This can only be changed if we stop translating the
    environment which we should in the future. Possible solution: make Fc
    completely independent, don't translate environment, traverse fc program
    twice, once to build environment, second time to type check
    * done

  * Elaboration of class declaration says that the method type needs to be
    elaborated as `(forall as. TC as => poly ty)`. In System Fc this is fine,
    but the haskell type can't look like this, so in practice we group the type
    abstraction variables and type class constraints with the implicit type
    variables and type class constraint so we have a valid haskell poly type and
    the corresponding System Fc type looks like this as well.

  * sprinkle it with freshener

  * superclass entailment as & bs are untouchables?

  * make Axioms and AnnSchemes SnocLists again

  * Value Binding Translation: the computed free unbound variables are the
    untouchables for the class constraint entailment, but are computed after
    entailment. => first equality than class cs?
    * they could become part of the abstraction, but some freshening needs
      to happen

  * refine residual class constraints with the resulting type substitution
    after OutSideIn(X), might not be required but let's be sure.

Substitution type class map
---------------------------

  * SubstVar v t x: substitute a single var ``x`` with ``t`` in ``x``
  * ApplySubst s t: apply full substitution ``s`` on ``t``
    not used much it seems
  * Subst dom img s: ``|->`` operator, construct single item subst
  * freshenLclBndrs: generate new vars for polymorphic types
