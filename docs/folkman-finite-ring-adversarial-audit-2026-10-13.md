# Folkman finite Boolean-ring maps — adversarial review (13 October 2026)

**Scope:** atom-level finite non-unital Boolean rings and the proposed
`FolkmanFiniteBooleanRingMaps.lean` module in PR #167.  This document does
**not** validate the full two-sorted Fraïssé amalgamation theorem.

## Algebraic check independent of Lean tactic elaboration

For partial fibre maps (f:B\to A\sqcup\{\bot\}) and
(g:C\to A\sqcup\{\bot\}), construct
(
 \Omega=\{(b,c):f(b)=g(c)\in A\}
 \sqcup\{\widehat b:f(b)=\bot\}
 \sqcup\{\widehat c:g(c)=\bot\}.
)
For (S\subseteq B), the left image consists of the compatible pairs
whose first coordinate lies in (S), together with the private points
(widehat b) for outside (b\in S); the right image is analogous.

Each atom of \(\Omega\) has exactly one left origin when it has a left
origin, and exactly one right origin when it has a right origin.  Therefore
membership in the image of \(S\cap T\), \(S\cup T\), or \(S\triangle T\)
is respectively conjunction, disjunction, or exclusive-or of the two
image memberships.  The embeddings preserve the non-unital Boolean-ring
operations \(0,\cap,\triangle\).  In this model a union of left
supports equals a union of right supports only when every selected
inside fibre is constant on both sides and all private outside atoms
are absent.  This is precisely the set-level strong intersection
proved in `FolkmanAtomAmalgam.lean`.

## Adversarial boundary cases

1. **Empty base (`A = ∅`).** Both source atom sets map to disjoint
   private points.  Ring embeddings remain injective and have only zero
   in their common image.  No invented base unit is required.
2. **Nonempty base fibres are essential.** If a base atom has a left
   preimage but no right preimage, its left row has no amalgam atoms.
   Thus the left map may send a nonempty atom subset to the empty set,
   losing injectivity.  The hypotheses \(\forall a\in A, f^{-1}(a)\ne\emptyset\)
   and \(\forall a\in A, g^{-1}(a)\ne\emptyset\) must remain explicit.
3. **Private points are essential.** With empty base and one outside
   atom on each side, omitting the private points makes both positive
   atoms map to zero, destroying injectivity and the strong
   intersection property.
4. **These are not unital embeddings.** In general, images of the
   greatest source elements do not equal the greatest element of the
   amalgam ring.  This agrees with the manuscript definition.

## Independent finite-model check

An exhaustive Python enumeration checked every pair of fibre maps with
all base fibres nonempty, for \(|A|\le 2\) and \(|B|,|C|\le 3\),
including the empty base and outside atoms.  It enumerated all subsets
on each side and verified both embeddings preserve intersection,
union and symmetric difference, are injective, and satisfy the
strong-intersection conclusion for every pair of image subsets.
**333 admissible configurations, 50,021 operation/intersection
comparisons, no failures.** This is a finite counterexample search,
**not** a proof of generality or a Lean kernel check.

## Validation update — 15 October 2026

The earlier Finset notation and dependent Option-pattern compilation
issues were repaired. The one-sort Boolean-ring maps, exact common-base
image (merged PR #171), two-sort ring diagram (merged PR #172) and
canonical zero-block pairing certificate (merged PR #173) have now
passed their respective Lean checks. The all-source-vector pairing
identities are present in the original green PR #174 and forward-ported
to clean PR #226, whose new branch still requires verification.

This is **not** yet a formal proof of the complete two-sorted
Folkman--BANANA amalgamation theorem: the bilinear form constructed in
canonical split coordinates must still be transported to the *actual*
atom-grid-plus-private-points Boolean-ring sorts.

A separate exhaustive small-model regression
(`scripts/check_folkman_pairing_extension_small.py`) writes the
pairing-preservation requirements as linear equations over F₂.
For 0 or 1 base atom on each sort, and 1 or 2 atoms on every
B/C sort, all **23,838 compatible pairings among 38,288 candidates**
admitted an extension on the actual atom-grid amalgam. The search
includes arbitrary pairing matrices, outside atoms, and empty base
sorts; it is a counterexample search, not a general proof.

## Reusable algebra for the missing bridge

It is preferable to reuse the already verified BANANA linear algebra
than to reproduce a new adapted-basis calculus for Folkman:

1. Express a finite Boolean-ring atom carrier `Finset I`, with
   addition symmetric difference, as the F₂-coordinate vector space
   `I → F2` by characteristic functions. Verify this is a linear
   equivalence; no multiplicative/unit compatibility is needed for
   extending a bilinear pairing, but the existing ring embedding
   proofs remain essential for the structure language.
2. Transport the two sortwise Folkman ring embeddings and the
   exact-common-image lemma to injective linear maps on those
   finite F₂-spaces. Their images must meet *exactly* in the common
   base; intersection merely on atoms would be insufficient without
   the proven ring-image intersection statement.
3. Reuse the linear retractions and bilinear pullback operations in
   `BananaArbitraryAmalgamTools.lean` and the redundant-coordinate
   construction in `BananaTripleCoordinates.lean` /
   `BananaTriplePairing.lean`, or equivalently transport the
   canonical block matrix from `FolkmanPairingExtensionCertificate.lean`.
   The common-base pairing is counted twice and must be subtracted;
   over F₂ this is the same as adding it once.
4. Choose complementary coordinates in the *ambient* Folkman
   atom grid and put zero pairing on all additional coordinates.
   Verify preservation on every pair of source vectors, not only
   on basis entries, then package the resulting two-sort structure
   and its embeddings.

This linearisation bridge is shared with the BANANA strong-amalgamation
proof. The partial `Option`-owner representation is specific to
Folkman and should not be collapsed into the total unital pre-BANANA
embedding definition. Likewise, the shared `FiniteOwnerSums`
module handles combinatorial sums, not the pairing transport itself.

## Remaining verification

- Finish and kernel-check the linearisation and full ambient pairing
  transport for the Folkman two-sort atom-grid diagram.
- Package finite strong amalgamation at the actual structure level,
  including pairing preservation, injection and exact intersection.
- Keep the Fraïssé-limit and ω-categoricity deductions separate.
- Proposed prose clarification (TODO only): say explicitly that the
  extended pairing restricts to the original pairing on **all**
  source vectors. The frozen circulation text is not edited here.
