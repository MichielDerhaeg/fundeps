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

  * Value Binding Translation
    - do nosig recursion
    - check if untouchable hack is no longer required

  * clean out old definitions like type constraints and unification vars

  * remove program expression from haskell and fc

  * parse quantified type contexts better

  * ~~actually check conditions~~
    - actually check ambiguous witness

  * error of `Tests/termination/CHRs27.hs` does not look like a bug, the
    residual constraint should end up in the type signature somehow, i see no
    other way than allowing the constraint to be quantified over. or removing
    it somehow through skolemization
    - probably should fail without signature

  * error of `Tests/termination/CHRs9.hs` is because of the mistake in the
    outsidein(x) spec, the orient rule should apply to this, even though the
    spec says it shouldn't, it says the left type should be a type pattern,
    which is untrue i believe

  * don't forget wel-formedness rules, etc for haskell and system fc in
    appendices

  * parsing typats does not support arrows, maybe drop typats all together, it
    does not seem very useful because we parse polytypes with normal monotypes,
    lets not go half way, we immediately convert to monotypes anyway
    - remove type patterns from impl, it's a theoretical construct

  * represent program as list of decls, core does this to, allows for nicer
    abstractions, cleaner as functions could simply return a list of Decl
    instead of precisely what is needed

  * finish wanted FD constraint generation

  * does topreactCls_w need to happen after topreactEqw? or can they be merged?
    - do it -Shia Labeouf

  * rule names required for solver rewrite rules?

  * fix inference syntax, does not correspond to rewrite rules

Substitution type class map
---------------------------

  * SubstVar v t x: substitute a single var ``x`` with ``t`` in ``x``
  * ApplySubst s t: apply full substitution ``s`` on ``t``
    not used much it seems
  * Subst dom img s: ``|->`` operator, construct single item subst
  * freshenLclBndrs: generate new vars for polymorphic types
