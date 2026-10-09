# Arbitrary BANANA strong amalgamation — proof and scope audit

**Date:** 9 October 2026. **Source:** `BananaTriplePairing.lean`.
The target theorem is
`SuccessorTree.NonPrecompact.BananaMatrixEmbedding.exists_strong_amalgam`.
Its Lean kernel/axiom audit is in
`BananaTriplePairingAxiomAudit.lean`. GitHub Actions run
[37924393977](https://github.com/janhubicka/lean-BANANA/actions/runs/37924393977)
first successfully compiled the terminal strong-amalgamation target.
The root-package import is being checked separately on this branch.

## Precise statement

For arbitrary finite standard-coordinate BANANA structures
`A=(L_A,R_A,β_A)`, `B`, `C`, and any BANANA embeddings
`f:A→B`, `g:A→C`, there is a finite BANANA structure `D`
with embeddings `i_B:B→D` and `i_C:C→D` such that

1. `i_B∘f=i_C∘g` on both vector-space sorts;
2. if `i_B^L(b)=i_C^L(c)`, then uniquely there is a common
   `a∈L_A` with `b=f_L(a)` and `c=g_L(a)`, and conversely;
3. the same exact intersection statement holds on the right sort.

No nondegeneracy or nonzero-dimension hypothesis is made. The
output has left coordinate dimension `aL+bL+cL` and right
coordinate dimension `aR+bR+cR`, with explicit parentheses.

## Desk review I — linear geometry (adversarial)

Choose linear retractions `p_B f=id`, `p_C g=id` on each
sort. The maps
`j_B(b)=(p_B b,b-f(p_B b),0)` and
`j_C(c)=(p_C c,0,c-g(p_C c))` are linear and injective
**even without retraction hypotheses**: from the image of
`j_B(b)` one recovers both `p_B b` and the remainder,
and hence `b`.

The retraction equations imply that `j_B(f(a))` and
`j_C(g(a))` are the common vector `(a,0,0)`.
If `j_B(b)=j_C(c)`, comparison of the B-only and C-only
coordinates gives both remainders zero. Comparison of the
first coordinate then gives `p_B b=p_C c=a`, so
`b=f(a)`, `c=g(a)`. This is exactly *strong*
amalgamation, not merely amalgamation or disjointness of
basis vectors.

Potential adversarial counterexample: the two source sorts
can have dimensions zero, and the pairing can be identically
zero; none of these steps use nondegeneracy. Distinct vectors
from different complements cannot collapse because all three
coordinate projections are recorded.

## Desk review II — bilinear pairing (adversarial)

On the redundant triple coordinates write `z=(a,u,v)`,
`w=(a',u',v')`. The proposed pairing is

```
  β_D(z,w) =
    β_B(f_L(a)+u, f_R(a')+u')
    + β_C(g_L(a)+v, g_R(a')+v')
    - β_A(a,a').
```

Each summand is bilinear; the subtraction removes the
duplicate contribution of `A`. Under the inclusion `j_B`,
the B-term becomes `β_B(b,b')`, the C-term becomes
`β_C(g_L(p_{B,L} b),g_R(p_{B,R}b'))`, and the A-term
equals `β_A(p_{B,L}b,p_{B,R}b')`. Since `g` preserves
the pairing, these last two terms cancel. Thus `j_B`
preserves all B-pairings, and symmetrically `j_C`
preserves all C-pairings.

The algebra does **not** assume that the selected retractions
themselves preserve the pairing. This is essential: a generic
linear splitting is not a morphism of bilinear systems.
It also makes no use of characteristic two in the
cancellation argument, although this Lean development
specialises to F₂.

The direct finite model regression
`scripts/check_strong_amalgam_arbitrary_small.py` already
passed 15,232 compatible diagrams, explicitly testing
pairing preservation, agreement and exact intersection.
Finite regression does not constitute a proof.

## Validation scope

The Lean theorem establishes **strong amalgamation for arbitrary
embeddings** in the standard-coordinate finite BANANA class.
The matrix definition and the embedding preservation of the
binary relation `E` are already formalised elsewhere.

This does not by itself establish all of
`BANANA/banana-class.tex`, Proposition `prop:fraisse`:
hereditary closure, joint embedding, the countable explicit
limit, its homogeneity and `ω`-categoricity require
separate formulation or translation to existing general
Fraïssé theorems.

The root build and the `#print axioms` outputs must
succeed before any green marker is added to the frozen
circulation manuscript. The only permitted manuscript
changes are TODOs and validation markers.

These are **two complementary adversarial desk analyses**,
not independently spawned referee reports. No available
connector can spawn genuinely independent adversarial
referee agents. Independent mathematical scrutiny remains
a separate task.
