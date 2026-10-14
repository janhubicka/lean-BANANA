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

## Compiler interface issue

Initial PR #167 compilation failed on unrecognised Finset operation
notation and dependent `Option` pattern matches.  The subsequent
revision specifies decidable equalities, uses the global `symmDiff`
rather than the nonexistent `Finset.symmDiff`, and repairs the two
dependent pattern witnesses.  These revisions must be checked with
the repository's pinned local Lean/Mathlib toolchain before any
`\leanverifiedpinned` marker is added.

## Outstanding proof interfaces

- Verify the revised `FolkmanFiniteBooleanRingMaps.lean` and its
  transitive axiom audit with a **local** root build.
- Package both sortwise Boolean-ring embeddings, their commuting
  base embeddings and the bilinear extension into one two-sorted
  structure, proving the strong image intersection at structure level.
- Keep the Fraïssé existence and \(\omega\)-categoricity deductions
  separate from the finite amalgam construction.
- Check clarity: the circulating text's choice of linear complements
  should explicitly say that the new pairing *restricts to the given
  pairings on all of* \(L_B\times R_B\) and \(L_C\times R_C\);
  this is a TODO proposal only, not approval to edit the frozen prose.
