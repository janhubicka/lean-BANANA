# BANANA — Track D: actual-subpair quotient atlas (6 November 2026)

Internal development note; NOT circulation prose. No TeX, TODO or
validation-marker changes. The circulation manuscript remains frozen.

## Status and reuse

**Draft / not Lean-kernel checked / not ready to merge.** This runtime has
neither Lean nor Lake and cannot resolve github.com; GitHub runners are out
of budget and have not been invoked.

The already merged module BananaFiniteFraisseProperties.lean proves
BananaMatrixStructure.exists_substructure_with_ranges: every pair of
actual vector subspaces is the exact pair of images of an embedding of
a finite matrix-coordinate pairing, with no nondegeneracy hypothesis.
We reuse it rather than duplicate the basis construction.

The staged class-family theorem from preceding Track D work supplies
coherent extensions for all isomorphisms between coordinate objects
when a representative and identifications have been chosen in one
common perfect pairing. This new atlas constructs those choices.

## New source

**BananaPresentedSubpairAtlas.lean**

- BananaMatrixEmbedding.coordinateDim_le derives both coordinate
  dimension inequalities from injectivity, using finrank monotonicity;
  the witness dimension l+r is not imposed as a new hypothesis.
- Every actual pair of subspaces admits a presented subpair, with
  exact image ranges, by the existing hereditary theorem.
- A Setoid classifies presentations by actual two-sorted
  pairing-preserving linear isomorphism. Its quotient chooses one
  representative per class and a representative-to-object isomorphism.
- exists_bananaPresentedClassCoherentExtension asserts a single coherent
  extension assignment on the presented groupoid in B_(l+r), covering
  identities, composable arrows, inverses and both sorts.
  This is staged Lean, not yet kernel-verified.

**BananaActualSubpairCoordinates.lean**

- An actual subpair consists of two vector subspaces of the fixed
  original BANANA structure.
- The presentation is chosen once per subpair; the image ranges equal
  the specified subspaces exactly.
- Genuine linear equivalences connect coordinate spaces with actual
  subspaces. An actual partial isomorphism is a pair of subspace linear
  equivalences respecting the restricted pairing, not arbitrary
  permutations.
- toPresentedIso converts such an arrow into a pairing-preserving
  matrix isomorphism between the fixed presentations, and
  same_presented_class places its endpoints in one quotient class.

Two AxiomAudit modules print transitive axioms for the new declarations.

## Remaining precise logical gap

The complete coherent-EPPA theorem for **actual** partial
automorphisms has not yet been exported. Apply the atlas coherent
family to each actual partial map via its once-selected
presentations. Prove conversion preserves identities, inverses,
and composition with quotient-class equality transports, and prove
the resulting ambient automorphism restricts to the correct maps
on actual vectors embedded through A into the common B_(l+r).

Do not infer this last groupoid-law theorem merely from the fact
that each individual partial automorphism extends. Choosing
different presentations for each arrow can spoil coherence.
The fixed-per-subpair selection is necessary, and its exact
algebraic compatibility still needs a kernel proof.

## Adversarial checks (not independent model referees)

- Separate invariant-based Python classification through total
  dimension four: 51 pairing matrices, 1,181 subpairs, 424
  isomorphism classes. For total dimension at most three,
  1,403 brute-force pair comparisons agree with rank-and-dimension
  classification, reproducing 135 subpairs and 81 classes.
- The earlier simultaneous-coherent-choice regression was rerun:
  17 pairing matrices, 1,277 partial isomorphisms,
  82,697 composable pairs; normal and optimised runs pass.
- Counterexample obligations: degenerate and one-sided pairings,
  zero subspaces, multiple coordinate presentations of the same
  actual subpair, inverse between different representatives,
  nontrivial base changes, and noncommutative multiplication order.

These checks are finite evidence, not Lean verification or
independently spawned adversarial referee reports.

## Exact-head local verification gate

Use the pinned Lean toolchain in a local checkout. Do not use
GitHub Actions. Commands:

    python3 scripts/check_lean_module_graph.py
    lake env lean BANANA/NonPrecompact/BananaPresentedSubpairAtlasAxiomAudit.lean
    lake env lean BANANA/NonPrecompact/BananaActualSubpairCoordinatesAxiomAudit.lean
    lake env lean BANANA/NonPrecompact/BananaMatrixCoherentOneClassAxiomAudit.lean
    lake build BANANA
    bash scripts/audit_all_axioms_local.sh
    python3 scripts/check_banana_presented_subpair_classes.py
    python3 scripts/check_banana_coherent_choices.py
    python3 -O scripts/check_banana_coherent_choices.py

Examine the exact Lean theorem binders, expected quotient casts,
all import dependencies and transitive axioms. Only propext,
Classical.choice and Quot.sound are permitted. Do not merge or
add circulation verification markers before exact-head kernel
builds and genuinely independent adversarial reviews succeed.
