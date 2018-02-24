Notes
=====

  * Fontend/HsTypes.hs:ftDropSuper puts local schemes first, they need to be
    prioritised because of super classes, don't forget to mention this.

  * Data constructor environment info carries polytypes instead of monotypes
    because the tycon and datacon info is translated and carried over into
    system fc and dictionary data constructors would have polytypes in haskell
    which is rather dirty. This can only be changed if we stop translating the
    environment which we should in the future. Possible solution: make Fc
    completely independent, don't translate environment, traverse fc program
    twice, once to build environment, second time to type check

  * Are local cls cs just AnnClsCs instead of AnnSchemes (Theory type)

Substitution type class map
---------------------------

  * SubstVar v t x: substitute a single var ``x`` with ``t`` in ``x``
  * ApplySubst s t: apply full substitution ``s`` on ``t``
    not used much it seems
  * Subst dom img s: ``|->`` operator, construct single item subst
  * freshenLclBndrs: generate new vars for polymorphic types
