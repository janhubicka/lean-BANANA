# Audit: one-sided BANANA copies are exactly subspaces

**Date:** 9 October 2026.
**Status:** mathematical and finite-model checks complete; the new Lean
files are **not kernel-verified** because Lean/Lake and the required
Mathlib/lean-successors checkout are unavailable locally. GitHub
Actions must not be used (runners are out of budget). No independent
referee agent was available; the two tests below are distinct
adversarial desk checks, not spawned referees.

## Proven target at the mathematical level

Let A be a finite BANANA structure, represented by a bilinear pairing
between finite vector spaces L_A and R_A.

* If R_A is zero, an unlabelled copy of A in **any** ambient BANANA
  structure C is exactly a subspace U of L_C with dimension dim(L_A).
* If L_A is zero, an unlabelled copy of A is exactly a subspace of R_C
  of dimension dim(R_A).
* Both correspondences commute with embeddings of ambient BANANA
  structures. They are genuine bijections, not merely injections into
  fixed-dimensional subspaces.

The zero-dimensional cases are included and require no positivity
condition. A zero **pairing** with both sorts nonzero is not one-sided;
it remains in the infinite-degree case.

## Adversarial desk check A — construction and pairing preservation

Given U ≤ L_C with dimension a = dim L_A and R_A=0,
choose a linear equivalence e:L_A ≃ U (finite dimensional spaces
over F₂ have bases and equal dimensions). Compose e with the
inclusion U ↪ L_C. On R_A use the unique linear map from the
zero space to R_C. Since β_A(x,0)=0=β_C(e(x),0), these maps preserve
the pairing for **arbitrary** β_C, not merely for a standard perfect
pairing. Both component maps are injective.

The image left subspace is exactly U because e is surjective.
The image right subspace is {0}. This produces a copy over every
candidate subspace, verifying surjectivity of
`BananaCopyRanges.leftFixedSubspace`; the converse injectivity
was already recorded in the merged
`BananaOneSidedCopyRanges.lean`. The right-only argument is
symmetric.

**Potential counterexample considered:** for a zero-dimensional
source, the only subspace of the requisite dimension is {0};
the induced structure has the two specified zero elements. No
additional images are introduced by the arbitrary pairing.

## Adversarial desk check B — functoriality and degree quantifiers

An ambient embedding f maps a left-only copy's left range U to
f.left(U), while its right range {0} remains {0}. This is exactly
`FixedSubspace.map`, by the already staged
`BananaCopyRanges.leftFixedSubspace_map` theorem. Hence the
bijections are natural with respect to ambient embeddings.

This confirms that colourings of **actual unlabelled copies**
and colourings of fixed-dimensional subspaces are equivalent
in the one-sided case. The earlier degree-one transfer proof
extends a colouring outside the injection's image; this is
valid even without surjectivity, but the new equivalence makes
the scope of the manuscript sentence fully explicit.

In contrast, this equivalence is false for two-sided sources,
where pairs of image subspaces must also have the prescribed
restricted pairing. The file does not claim otherwise.

## Finite regression

`scripts/check_copy_subspace_bijection.py` exhaustively checks
binary coordinate subspaces in dimensions 0–4. For each dimension
a and ambient n, the number of embeddings representing any fixed
a-dimensional subspace equals |GL(a,2)|, so the unlabelled image
is independent of the chosen source basis. Further tests verify
image transport through nested injective linear maps.

The local test passed:

- **91 distinct subspaces** over dimensions 0–4;
- **23,137 coordinate embeddings** grouped by their image subspaces;
- **37,130 composition/naturality checks**.

These tests do not establish any Lean theorem.

## Lean compilation/axiom obligations

1. In a local checkout at the pinned Lean toolchain
   `leanprover/lean4:v4.35.0-rc3`, build
   `BANANA/NonPrecompact/BananaOneSidedSubspaceEquivAxiomAudit.lean`.
2. Check the new equivalence declarations and the imported
   `BananaOneSidedCopyRanges` and
   `BananaOneSidedCopyDegree` modules. The currently staged
   `BananaCopyDegree` dependencies must also compile.
3. Inspect each transitive `#print axioms` result and ensure
   there are no `sorryAx` or additional unproved assumptions.
4. Only then import the new modules in root `BANANA.lean` and
   consider a green manuscript validation marker. Until then
   the circulation TODO from BANANA PR #164 stays in force.

## Reconciliation with concurrent work

Open lean-BANANA PR #12 contains an alternative copy/subspace
implementation, but its declaration names overlap with the
already merged PR #13. The useful extra idea in PR #12 was
surjectivity of the copy-to-subspace correspondence; this
branch implements that as a separate module with no conflicts
and strengthens it from perfect pairings to **all** ambient
BANANA structures. PR #12 should not be merged as-is.

The circulation part of the paper was **not edited** in this
branch. Any future manuscript adjustments remain restricted
to TODO notes and validation markers.
