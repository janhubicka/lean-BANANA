# BANANA one-sided copy-degree formalisation audit

**Date:** 9 October 2026 (Prague local time).
**Status:** staged, not kernel-verified. This is an adversarial desk
review; independent agent referees could not be spawned with the
available tools. No GitHub Actions were used.

## Target statement

The circulation manuscript states that a finite BANANA structure
`A=(L_A,R_A,β_A)` has copy Ramsey degree exactly one if either
`L_A` or `R_A` is zero, and infinite degree otherwise.
The two-sided part is staged in `BananaCopyDegree.lean`.
The current branch supplies the one-sided part in the **same**
`BananaCopyRanges` representation and combines both parts
in `BananaMatrixStructure.copyRamseyDegree_classification`.

The proof uses the **unconditional** finite binary subspace Ramsey
theorem already obtained from the successor-tree development in
`BinaryWord.leftOneSidedCopyRamseyOne_via_successors` and its right
counterpart. It adds no Ramsey axiom.

## Adversarial mathematical check A: identification of copies

For a left-only source of dimension `a`, every embedding into
an ambient `C` sends the zero-dimensional right sort to `{0}`.
The image of the left sort is an `a`-dimensional subspace of
`C.left`. Conversely, a copy's two image sets are determined by
that left subspace and the obligatory right singleton. Therefore
two copies with the same left subspace are equal.

`leftFixedSubspace` extracts the subspace by choosing *any*
embedding representing the unlabelled copy. Its underlying
submodule is independent of the choice: membership is exactly
membership in the copy's left image set. The analogous result
holds with left/right exchanged. Ambient embeddings take these
subspaces to their ordinary images, as required for the
Ramsey-arrow quantifiers.

**Potential counterexample considered:** sources with zero pairing
but both sorts nonzero are *not* one-sided; the correspondence
does not apply to them and correctly leaves them in the infinite
degree case. Sources with both sorts zero have the unique
zero subspace on each side and degree one.

## Adversarial mathematical check B: transfer of colourings

The existing GLR interface quantifies over arbitrary colourings of
all `a`-dimensional subspaces, while the manuscript quantifies
over colours of **realisable unlabelled copies**. These domains
need not be identified by a surjective map for the proof:
a colouring of copies can be extended to all fixed subspaces
by assigning a fallback colour outside the range of
`leftFixedSubspace` (or `rightFixedSubspace`).

The representation map is injective, so the extended colouring
agrees with the original colouring at every copy. The
naturality lemma transports monochromaticity under the target
embedding chosen by GLR. In particular **no unproved surjectivity
of a copy-to-subspace map is assumed**.

**Degree zero exclusion:** taking target `B=A` with one available
colour forces a nonempty copy image in every Ramsey witness.
A bound of zero would force the chosen colour set to be empty.
Thus the optimal one-sided copy degree is exactly one rather
than merely at most one.

## Regression

The independent Python finite-space enumerator
`scripts/check_one_sided_copy_ranges.py` passed locally.

- 81 ambient/source dimension quadruples, including dimensions 0;
- 3,969 pairs of injective ambient sort maps;
- 63,756 source-copy/subspace and embedding-transport checks;
- the correct binary subspace counts through dimension four:
  `[1]`, `[1,1]`, `[1,3,1]`, `[1,7,7,1]`,
  `[1,15,35,15,1]`.

The enumeration only checks small finite models; it is not a proof
of the general copy Ramsey theorem. Since a one-sided source's
pairing is necessarily zero, every tested ambient pairing is
covered without needing to enumerate separate matrices.

## Static and kernel-validation checklist

* The newly added Lean files contain no `sorry`, `admit`,
  `axiom`, `constant`, or `opaque` declarations.
* The branch must **not** change the root `BANANA.lean`.
* Build the targeted module locally:
  `lake env lean BANANA/NonPrecompact/BananaOneSidedAxiomAudit.lean`.
  The project uses `leanprover/lean4:v4.35.0-rc3`, with its pinned
  `lean-successors` dependency.
* Check `Submodule.ext`, `Subsingleton.elim`, range-membership
  simplifications, finrank-of-range and finite-image lemmas against
  Mathlib. Then inspect every transitive `#print axioms` output,
  particularly that `sorryAx` is absent.
* Previously staged two-sided `BananaCopyDegree.lean` also needs a
  successful local build: the unified classification theorem imports it.
* Only after a successful build may `BANANA.lean` import these
  modules and the manuscript receive a green validation marker.
  Until then, preserve the circulation prose and use a TODO,
  not a certificate.

No compiler was available in the isolated container, and outbound
DNS is disabled. The code is therefore a meaningful formalisation
patch, **not** a completed kernel check. No proof-claim is upgraded
by this audit.
