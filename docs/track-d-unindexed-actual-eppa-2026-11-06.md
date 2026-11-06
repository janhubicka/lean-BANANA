# BANANA Track D — actual-subpair coherent EPPA (6 November 2026)

INTERNAL ONLY. The circulation text remains frozen and has not been modified.
This continuation is STAGED SOURCE, NOT a Lean kernel verification.

## New proof chain

1. BananaActualSubpairFunctor.lean adds identity, composition and inverse
   for genuine two-sorted pairing-preserving isomorphisms between actual
   subspaces. It proves that the ONCE-CHOSEN coordinate presentations
   preserve identity, composition and inverse, and checks both coordinate
   maps on points. No per-arrow fresh basis selection occurs.
2. BananaActualSubpairClassCoherence.lean pulls the previously staged
   coherent isomorphism-class family back to the type of ACTUAL subpairs
   carrying their common isomorphism-class index. The class-indexed action
   extends original partial maps on left and right inside the same
   perfectBanana(l+r).
3. BananaActualSubpairUnindexedCoherence.lean removes the quotient index
   from the action. An arrow p:U -> V specifies the source class and the
   induced equality of source/target class indices. A dependent
   change-of-index lemma proves the ambient extension does not depend
   on proof witnesses. Identity, inverse and composition survive descent.
   The staged theorem exists_bananaActualCoherentEPPA has ONLY A as
   a mathematical parameter. Its fixed witness has left and right
   dimension dim(A.left)+dim(A.right), with all partial isomorphisms
   extended coherently.
4. BananaActualSubpairUnindexedCoherenceAxiomAudit.lean prints transitive
   axiom sets for all new proof declarations. These queries have not
   been run through Lean.

The concrete finite BANANA automorphism group represents the faithful
two-sorted pairing-preserving linear automorphisms of a finite matrix
pairing. An actual substructure is precisely two vector subspaces. No
nondegeneracy, positive-dimensional, ordering, naming of bases or other
extra assumption was introduced.

## Adversarial mathematics

Statement-fidelity pass: the end-to-end theorem now quantifies over
ALL actual subpairs U,V and every genuine partial isomorphism p:U -> V
and assigns ONE ambient automorphism Theta(p). Identity maps extend as
the identity; for composable p and q it asserts Theta(q)*Theta(p)=
Theta(p.trans q). The fixed embedding of A into perfectBanana(l+r)
is used to state extension on every vector of both sorts.

Counterexample pass: source and target classes may carry different
*proofs* of equality even when the class indices coincide. The
changeIndex lemma is intended to address this through dependent
rewriting and proof irrelevance. Wrong group multiplication order
or an independent basis choice per arrow breaks the formula. Empty
dimension in this project means the zero vector space with one
zero vector, never an empty carrier. Degenerate pairings are included.

The independent finite script check_banana_actual_coordinate_functor.py
enumerates all pairing matrices with total dimension <= 3, all
135 actual subpairs, all 1,277 actual isomorphisms (and inverses)
and 82,697 composable pairs; object-dependent, deliberately
noncanonical bases are held fixed per subpair. The identity,
inverse, composition and restricted-pairing checks all passed in
normal and Python -O modes. A separate deliberately WRONG midpoint
basis choice fails the functoriality equation.

This is finite adversarial evidence, NOT an independently spawned
mathematical referee. No model-referee tool is available in this
runtime. This code has not been elaborated and no Lean theorem can
yet be labelled kernel-verified.

## Validation gate — do not merge this draft

There is NO local Lean/Lake toolchain available, and direct GitHub
network access in the container failed DNS resolution. GitHub
Actions are out of budget. No runners were started.

At the exact PR head, with the pinned Lean toolchain and dependencies,
run locally:

    python3 scripts/check_lean_module_graph.py
    lake env lean BANANA/NonPrecompact/BananaActualSubpairUnindexedCoherenceAxiomAudit.lean
    lake build BANANA
    bash scripts/audit_all_axioms_local.sh
    python3 scripts/check_banana_actual_coordinate_functor.py
    python3 -O scripts/check_banana_actual_coordinate_functor.py
    python3 scripts/check_banana_coherent_choices.py

Check every transitive axiom and allow only propext,
Classical.choice and Quot.sound, and independently check the exact
Lean binders against the frozen circulation statement. The imports
from previously unverified draft PR #310 require compilation too.
The main BANANA.lean import file was deliberately left unchanged to
avoid conflicts with parallel tracks.

No changes to manuscript TeX, published prose, TODOs, validation
markers, appendices, or workflows were made in this continuation.
After a successful exact-head build, record the theorem SHA and add
only the permitted validation marker to the frozen circulation part.
