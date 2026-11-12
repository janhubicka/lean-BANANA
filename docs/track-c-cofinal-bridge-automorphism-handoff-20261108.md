# BANANA Track C — cofinal bridge endpoint (8 November 2026)

**Internal only. No circulation prose or appendix edits.**
The source changes are draft mathematical implementations; they have
NOT passed the pinned Lean kernel build, transitive axiom audit or
independent adversarial referee certification.

## Where the mathematical proof now ends

Given a countable Folkman two-sort pairing with a *coherent exhaustive
back-and-forth sequence* of finite pointed copies of the same atom
codes, the induced maps on the full ambient left and right rings
assemble into a single genuine pairing-preserving automorphism.
The actual construction of the cofinal sequence, starting from each
finite generated-substructure isomorphism, remains the final
unimplemented countable-limit/back-and-forth obligation.

The new source modules are:

- FolkmanCofinalBridgeChain.lean: a typed interface for a sequence
  of finite two-sort codes, each embedded twice into the original
  non-unital ring pairing. Both copies must reconstruct the SAME
  atom-matrix pairing on all code elements, and all four embeddings
  must be injective. The sequence has source/target coherence
  in both directions, common refinements on each ring sort and
  across the sorts, and exhaustion of both copies on both ambient
  sorts. The equality of stage pairing values is derived from
  the two matrix-reconstruction fields.
- FolkmanCofinalBridgeAutomorphism.lean: given these exact
  hypotheses, the two global forward maps are injective and
  surjective, preserve addition and multiplication in the
  original non-unital language, and preserve the full F₂ pairing.
  Two ring equivalences form an actual global automorphism.
- FolkmanCofinalBridgeHomogeneity.lean: a labelled tuple pair
  is represented in one bridge, and the global automorphism
  extends that labelled map. The remaining premise
  FolkmanHasCofinalBridgeExtensions requires such a chain for
  each finite generated-structure isomorphism. From that
  premise the already prepared generated-homogeneity theorem
  and finite true global orbit quotients follow.

This interface does NOT assert the existence of the required
countable Folkman limit or coherent exhaustive chains.

## Two independent finite semantic regressions

These scripts were executed locally and are committed to the draft
branch. They are not Lean proof checks or independently spawned
adversarial proof referees.

1. check_folkman_cofinal_bridge_automorphism.py:
   Exhaustive finite full-code bridge tests for up to three atoms in
   each sort, all pairing matrices and all atom permutations:
   20,165 configurations; 1,717 pairing-preserving cases and
   18,448 rejected non-pairing-preserving cases. It checked
   1,231,613 original pairing values and 4,983,896 operation
   preservation identities.
2. check_folkman_two_stage_bridge.py:
   Nontrivial smaller first stages represented by partial atom
   owners, followed by a full ambient stage. It passed 1,717
   two-stage configurations, 41,956 pairing comparisons and
   258,788 operation identities, including 821 configurations
   with a zero source sort and 1,426 with unowned ambient atoms.

Both scripts fail closed under python -O and are now included
in the exact-head local verifier. These finite semantics do not
certify Lean syntax, elaboration, or transitive axioms.

## Precise remaining proof obligations

1. Compile and inspect every new declaration with pinned local
   Lean 4.35.0-rc3, run the complete transitive axiom audit,
   and obtain genuinely independent adversarial proof referees.
2. Verify Track B drafts #305 and #309, especially native finite
   heredity (intrinsic units), countability, JEP and strong AP.
3. Construct the actual countable Fraïssé limit in Lean, or
   supply a genuine general existence theorem. The pinned Mathlib
   Fraisse module explicitly lists existence as a TODO.
4. Prove the one-point forth/back extension of finite *paired*
   bridges from the limit's finite extension property. Dovetail
   both sorts and both copies, preserving the full pairing and
   all original non-unital ring operations.
5. Show that the resulting coherent exhaustive chain starts with
   a bridge representing each specified finite generated
   isomorphism. This discharges the exact premise
   FolkmanHasCofinalBridgeExtensions.
6. Apply the already prepared exact global orbit classification,
   cite Ryll–Nardzewski as the standard model-theoretic conclusion.

A finite non-homogeneous Boolean ring provides a counterexample to
the converse without generated homogeneity: equal one-generator
profiles need not imply ambient automorphism conjugacy.

**No GitHub Actions were dispatched. The manuscript was not changed
or green-marked. Keep PR #308 draft and unmerged.**
