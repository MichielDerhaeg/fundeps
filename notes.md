Notes
=====

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

  * ~~error of `Tests/termination/CHRs9.hs` is because of the mistake in the
    outsidein(x) spec, the orient rule should apply to this, even though the
    spec says it shouldn't, it says the left type should be a type pattern,
    which is untrue i believe~~
    - does not terminate because conditions are insufficient, GHC has same
      issue with UndecidableInstances

  * parsing typats does not support arrows, maybe drop typats all together, it
    does not seem very useful because we parse polytypes with normal monotypes,
    lets not go half way, we immediately convert to monotypes anyway
    - remove type patterns from impl, it's a theoretical construct

  * represent program as list of decls, core does this to, allows for nicer
    abstractions, cleaner as functions could simply return a list of Decl
    instead of precisely what is needed

  * ~~finish wanted FD constraint generation~~
    - general transClose FD relation

  * does topreactCls_w need to happen after topreactEqw? or can they be merged?
    - do it -Shia Labeouf

  * projection arrow

  * projections in axioms

Text TODOs
==========

  * mention no kinds in source

  * don't forget wel-formedness rules, etc for haskell and system fc in
    appendices

  * rule names required for solver rewrite rules?

  * cite that one paper about reasoning about type families in both directions
    and talk about it in entailment

  * better explain why match contexts, can't return coercions

  * transitive closure superclass fds in det() and mention DAG, superclass
    entailment

  * are untouchables passed everywhere?
    - subsumption needs untchs: abs
    - superclass entailment needs untchs: abs

  * fix inference syntax, does not correspond to rewrite rules
