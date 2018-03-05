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

  * Are local cls cs just AnnClsCs instead of AnnSchemes (Theory type)

  * Why lookup fc variant of tycon and datacon names when their name is the
    same? This requires their elaboration to be monadic without good reason.
    - Just rewrap names.

  * To do type reduction, I would need something very similar to unification to
    match the axioms and produce the substitution. I could use the old
    unification, modified to not reduce type families, use the actual
    unification and this would make the ``ArgR`` rule redundant I presume, or
    use something custom but very similar to unification for this specific
    case. The latter would mean traversing two types, they would always have to
    match exactly the same except for TyVar's, in this case a substitution
    would be created from this tyvar to the other type. We would need to check
    if this substitution has already been created. I might be missing something
    else.
    - use old unification

  * Elaboration of class declaration says that the method type needs to be
    elaborated as `(forall as. TC as => poly ty)`. In System Fc this is fine,
    but the haskell type can't look like this, so in practice we group the type
    abstraction variables and type class constraints with the implicit type
    variables and type class constraint so we have a valid haskell poly type and
    the corresponding System Fc type looks like this as well.

Substitution type class map
---------------------------

  * SubstVar v t x: substitute a single var ``x`` with ``t`` in ``x``
  * ApplySubst s t: apply full substitution ``s`` on ``t``
    not used much it seems
  * Subst dom img s: ``|->`` operator, construct single item subst
  * freshenLclBndrs: generate new vars for polymorphic types
