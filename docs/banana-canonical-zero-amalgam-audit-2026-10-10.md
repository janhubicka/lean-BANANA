# Canonical zero-base amalgamation: mathematical and Lean audit

**10 October 2026.** This is an internal proof audit for the circulation
DEERP corollary, not a new statement in the frozen manuscript. The
new declarations live in `BananaDirectSumCanonical.lean`.

## Scope and external criterion

The published Hrushovski–Krupiński–Pillay paper *On first order
amenability*, Selecta Mathematica **32** (2026), article 23,
Proposition 2.17, assumes an ω-categorical Fraïssé limit of a class
having **canonical amalgamation over the empty-generated
substructure**. For embeddings `f:B→C`, this requires a compatible
embedding `A⊗B→A⊗C` commuting with the canonical inclusions.
The theorem then concludes *first-order* extreme amenability, not
extreme amenability of the Polish topological group. The further
equivalence with DEERP is cited from Krupiński–Lee–Moconja,
Theorem 3.16.

Because BANANA has named zero constants on two sorts, the
empty-generated substructure is the two singleton-zero spaces.
The direct sum is an amalgam over precisely those two elements.

## Geometric adversarial check

For arbitrary finite binary pairings `A=(L_A,R_A,β_A)` and
`B=(L_B,R_B,β_B)`, take
`L_D=L_A⊕L_B`, `R_D=R_A⊕R_B` and
`β_D((x,x'),(y,y'))=β_A(x,y)+β_B(x',y')`.

The canonical embeddings send vectors on each sort to `(x,0)`
and `(0,y)`. If `(x,0)=(0,y)`, both are zero. Hence the
images intersect only in the empty-generated substructure,
**separately on both sorts**. Both pairings restrict exactly
to the originals. Both cross-pairings vanish. In particular
this is not a set-theoretic disjoint union that forgets
named constants: the zero elements are identified correctly.

Potential counterexamples checked algebraically: a zero-dimensional
sort, both sorts zero-dimensional, and an identically zero or
degenerate pairing. All are handled without a nondegeneracy
hypothesis. The direct sum is a strong amalgam over the generated
empty structure, not an arbitrary-cospan amalgam.

## Functorial adversarial check

For embeddings `f:A→A'` and `g:B→B'`, the product embedding
is `f⊕g`, acting on the two coordinate blocks separately.

The four naturality equations are:

```
  (f⊕g) ∘ inl_A = inl_A' ∘ f    (on left and right sorts),
  (f⊕g) ∘ inr_B = inr_B' ∘ g    (on left and right sorts).
```

They are genuine equations of linear maps, not only of pairings.
The earlier `BananaDirectSum` module already established that
`f⊕g` preserves the complete pairing and that direct sum respects
identity and composition on the two sorts. Thus the construction
satisfies the *one-sided embedding compatibility* required in
Proposition 2.17 (take `f=id_A` and arbitrary `g`).

A potential modelling objection is that a mere choice of some
strong amalgam would not be canonical. Here the coordinate
construction and the induced map `f⊕g` are explicitly defined;
naturality is asserted and kernel-checked rather than inferred
from the existence of an amalgam.

## Precise validation boundary

The seven terminal declarations audited in
`BananaDirectSumCanonicalAxiomAudit.lean` prove two exact
intersection equations, four naturality equations and a package
for the strong zero-base amalgam. All seven must compile with
only the standard Lean axioms
`{propext, Classical.choice, Quot.sound}`, without `sorryAx`.
The module has been added to the root import graph *on its PR
branch*; a green root build is required before merging.

This proves the **finite algebraic hypothesis** of the cited
published proposition. Neither the global invariant-type
conclusion nor the DEERP equivalence is re-proved in Lean.
Those are external cited model-theoretic theorems, as appropriate
for a circulation-quality paper accessible to readers beyond
structural Ramsey theory.

No source inside the circulation part of BANANA is changed
by this PR. After kernel verification the only allowed
manuscript action is a targeted validation marker or TODO.
This is a desk audit in two complementary approaches;
it is **not** a pair of separately spawned referees.
