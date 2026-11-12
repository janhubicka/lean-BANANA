# Track C — one-point bridge reduction and verification boundary
8 November 2026 — internal mathematical and source-level handover

**No circulation prose, appendix, TODO or validation marker was changed.**
These are drafted Lean proofs, not kernel-certified theorems.

## Upstream dependency status

Finite native Folkman PRs #305 and #309 are now merged into main
as of 8 November. Their APIs for finite pairing objects, exact
non-unital embedding witnesses, heredity (with intrinsic finite
subring units), JEP and strong amalgamation can be reused by Track C.
Their being merged does **not** certify the present Track C branch
or prove that all final merged declarations passed an axiom audit.
No GitHub Actions were triggered in this continuation.

## Reduction achieved in source

The original cofinal-bridge interface required a complete
two-sided exhaustive sequence with representative coherence,
common-stage comparisons on both sorts and compatibility of the
original cross-sort pairing. Four new modules make the source of
this elaborate sequence explicit:

1. FolkmanFinitePairedBridgePreorder:
   A finite bridge has an atom-coded finite source stage and a
   second embedding of the SAME code into the ambient original
   non-unital rings. Both source and target reconstruct every
   value of the original F₂ pairing by the same atom matrix.
   An extension is two injective non-unital ring homomorphisms
   commuting with all FOUR source and target maps. Identity,
   composition and a preorder are constructed. The equality of
   atom matrix pairings is checked on both source and target sides;
   it is a CONSEQUENCE of the faithful original pairing diagrams.

2. FolkmanFinitePairedBridgeCofinal:
   The one-point extension property says that any finite paired
   bridge can be enlarged to cover any given original ambient
   element in the SOURCE/LEFT, SOURCE/RIGHT, TARGET/LEFT or
   TARGET/RIGHT image, preserving all old data. Under countability
   of both sorts, the already used Mathlib
   Order.sequenceOfCofinals lemma fairly schedules the four
   families of cofinal requirements. A monotone sequence of
   actual finite paired bridges exhausts all four copies.

3. FolkmanFinitePairedBridgeToCofinalChain:
   For each pair of finite-stage indices n,m, move to k=max(n,m)
   and choose the two genuine extension maps. Their commuting
   squares give the common-left, common-right and cross-sort
   common-stage witnesses; injectivity in the source/target
   copy gives both directions of representative coherence.
   This constructs ALL fields of the existing
   FolkmanCofinalBridgeChain, including the exact atom matrix
   pairing in both copies. The Type-valued construction now
   correctly uses Classical.choose on the Prop-valued existence
   theorem for the monotone sequence.

4. FolkmanOnePointBridgeHomogeneity:
   A concrete INITIAL finite paired bridge records both copies
   of each labelled generator. Starting the cofinal sequence at
   that bridge gives a coherent exhaustive chain extending the
   original tuple map. The previous theorem then constructs
   one actual global pairing automorphism. Consequently the
   same two assumptions — four one-point extensions, and the
   existence of an initial finite bridge for each generated
   isomorphism — imply genuine generated homogeneity, finite
   two-sort global orbit quotients and finite tagged mixed-sort
   orbit quotients.

The starting bridge need not be a whole ambient finite stage:
it should code the finite GENERATED non-unital subrings, with
their intrinsic identities. Choosing an arbitrary larger finite
stage can be invalid because the two finite ambient stages can
have unequal atom multiplicities despite the equality of
generated-type profiles.

## Adversarial mathematics

An initial bridge representing a finite generated isomorphism,
and the four one-point extensions, are both necessary hypotheses
of the new construction. They cannot be inferred from finite
profile equality or local finiteness in an arbitrary nonhomogeneous
model. For example a singleton and a doubleton in a finite
three-atom Boolean ring generate isomorphic one-atom non-unital
subrings but cannot be exchanged by a global ambient
automorphism. The one-point extension property appropriately
fails for a suitable finite paired bridge in that ambient ring.

A separate Python finite-model checker used partial atom owners
and independently selected zero-pattern omissions in a
three-level refinement of **both** ring sorts. It checked:

- 1,717 ambient pairing-preserving atom-permutation symmetries;
- 1,717 actual three-stage finite bridge chains;
- 167,728 stage-pairing evaluations;
- 94,529 extension pairing comparisons;
- 85,898 commuting original-source/target ring squares;
- 12,039 nontrivial composition comparisons and 28,216
  identity comparisons;
- 111 chains with a zero initial source sort and 1,357
  with initially unowned ambient atoms.

The regression passed and explicitly refused Python -O.
Exact standalone source SHA-256:
0e454ba3eeca60978b68be1efdf495698022124850908ddcba694d7b962c21f8.
This is FINITE SEMANTIC EVIDENCE, not a Lean proof or independent
agent referee. No independent referee agent could be spawned
through the current tools.

## Remaining tasks to finish the formalisation

1. Verify the exact Track C source by the PINNED local Lean toolchain,
   in dependency order, then build BANANA and inspect every
   transitive #print axioms result. The current runtime contains
   no lean, lake or elan and cannot resolve github.com.
   The local-only exact-head verification shell script now lists
   the new paired bridge modules explicitly and never dispatches
   GitHub Actions.

2. Construct the actual countable two-sorted Folkman Fraïssé limit
   (or add an adequately general, verified existence theorem).
   The pinned Mathlib Fraisse module lists existence as a TODO.
   Prove the embedding extension property for its finite objects,
   with the original pairing on all elements.

3. Discharge the FOUR one-point finite paired bridge extension
   claims using finite generated extensions, the genuine
   original-language strong amalgamation from Track B, and the
   countable limit's embedding extension property. Only the
   paired diagram, not a bare atom embedding, suffices.

4. Construct one INITIAL bridge representing each given isomorphism
   of actual generated two-sort subrings. Use the intrinsic finite
   subring units from Track B when coding them as finite
   Boolean rings; never require the ambient unit to be preserved.

5. Deduce the existing conditional genuine orbit criteria.
   Ryll–Nardzewski remains the externally cited, standard
   omega-categoricity consequence. Obtain independent
   adversarial proof referees before any green manuscript
   validation marker or merge.

**Draft PR #308 must remain unmerged until all verification gates
are met.** The mathematical route is complete conditionally;
the actual countable-limit construction and exact-head kernel
verification remain open.
