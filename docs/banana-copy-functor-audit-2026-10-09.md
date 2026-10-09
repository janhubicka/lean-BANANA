# Functoriality and palette-pullback audit for unlabelled BANANA copies

**Date:** 9 October 2026. **Status:** mathematically reviewed and
tested on finite binary systems; Lean source **not kernel-verified**.
There is no local Lean/Lake executable and external DNS cannot resolve
GitHub. No GitHub Actions were run. No independent referee agent was
available; the two adversarial checks below are separate manual
analyses, not independently spawned reports.

## Statements and scope

The source `BananaCopyRanges` represents an unlabelled copy of
`A` in `B` by the pair of its finite left and right image sets,
with a witness that they are the ranges of a BANANA embedding.
An ambient embedding `f : B → C` acts by taking the image of
each range.

`BananaCopyFunctor.lean` adds five statements:

1. `BananaCopyRanges.map_comp`: taking images respects composition.
2. `BananaCopyRanges.map_identity`: the identity fixes a copy.
3. `BananaCopyRanges.map_injective`: an ambient embedding cannot
   identify distinct unlabelled copies.
4. `BananaLinePairCopy.exists_preimage_of_in_mapped_copy`:
   a nonzero line pair inside the image of a copy has a line-pair
   preimage inside the original copy, of the *same pairing value*.
5. `BananaCopyRanges.linePairPalette_map`: for any colouring of
   line pairs in `C`, the set of colours inside `f(D)` equals
   the set obtained inside `D` by pulling that colouring back
   through `f`.

These statements do not rely on a Ramsey theorem and work for
arbitrary finite BANANA pairings and either pairing value `b`.
The source `A` itself may have a degenerate pairing or
zero-dimensional sorts. No source automorphisms are chosen.

## Adversarial check A: geometry and quantifiers

The left/right ranges of `f(D)` are `f_L(L_D)` and
`f_R(R_D)`. An ambient embedding is injective in each sort, so
equal image ranges imply equal original ranges. Under composition,
each image set is taken through the composed linear map, which is
the same as two successive image operations.

Suppose `(u,v)` is a nonzero line pair inside `f(D)`. There
exist `x∈L_D`, `y∈R_D` with `f_L(x)=u`, `f_R(y)=v`.
Injectivity implies that `x,y` are nonzero. Pairing
preservation gives `β_B(x,y)=β_C(u,v)`, so `(x,y)`
has the same prescribed pairing value as `(u,v)`.
This proves the preimage claim, including the edge cases
where `D` or the ambient structure has a zero-dimensional
sort (the quantified line-pair set is then empty).

**Potential objection tested:** the vector pair might lie in the
two image ranges but fail to represent a source line pair.
This cannot happen: the restriction of the pairing on the
image ranges is the source pairing, and the two preimage
vectors have the required pairing value by preservation.

## Adversarial check B: colours and source automorphisms

The line-pair palette of a copy `D` is defined by *all*
contained line-pair copies. This is invariant under a change
of basis or a source automorphism and is not an arbitrary
representative's colour. Every line pair in `D` maps to one
in `f(D)`; the preimage result above gives the converse.
The colour set inside `f(D)` is therefore *exactly*
the image of the pullback colouring on pairs inside `D`.

**Potential objection tested:** the displayed equality might
hold only when the ambient colouring is invariant under
embeddings. No such invariance is assumed or needed. The
pulled-back colouring is `c(P) := c_C(f(P))`; arbitrary
ambient colours are allowed.

This is the precise compatibility needed when transferring
the persistent-colouring argument to unlabelled copies.

## Independent finite regression

`scripts/check_copy_functor_small.py` is a standalone,
reproducible Python script. For finite coordinate binary
spaces, it enumerates injective left/right linear maps,
all possible source copy ranges, and small ambient pairing
matrices. The source pairing is always the pullback of the
ambient pairing along the chosen maps, so each tested map
is genuinely pairing-preserving. Two non-invariant ambient
colourings are used to test exact palette equality for both
possible pairing values.

Local test outcome:

- **2,558,464** exact line-pair palette comparisons passed;
- **70,756** copy-image injectivity cases across **34,993**
  embedding/ambient-pairing combinations;
- **92,416** copy-image composition checks.

For matrices with at most sixteen possibilities, all are
checked; for larger matrices a deterministic variety of
small and extremal matrices is checked. This is regression
evidence, not a universal mathematical proof and not a
Lean kernel check.

## Follow-up

Run locally, with the pinned toolchain and Mathlib:

```sh
lake env lean BANANA/NonPrecompact/BananaCopyFunctorAxiomAudit.lean
```

The `scripts/check_staged_ramsey_degrees.sh` audit now includes
this module. It must succeed, and every printed transitive
axiom set must be inspected, before the new declarations may
be called verified. Do not add a green circulation marker yet.

No circulation text is modified in this branch. Existing
circulation TODOs remain accurate.
