# Binary successor-tree → binary GLR: adversarial audit

Date: 7 October 2026. Working branch: `formalize/glr-via-successor-exact`
in `janhubicka/lean-BANANA`. This is **not** a completed Lean certificate.

## Verified external input

The finite exact-terminal successor-tree theorem
`SuccessorTree.SMTree.shapeRamsey_exact` is supplied by
`janhubicka/lean-successors`, pinned in the working branch to
`d9be105f73ca5a0f3f411b87d4c2419d0eb94753`. That dependency
passed its full Lean integration check.

The generic transport in `BinarySubspaceRamseyFromSuccessor.lean`
assumes a `BinarySubspaceSuccessorEncoding` and concludes
`BinarySubspaceRamsey`. **No proof of the concrete encoding is being
claimed** merely from the existence of the successor-tree theorem.

## Algebraic audit (M1–M3)

The intended tree is the binary prefix tree with a bit-labelled successor
and empty parameter list. The distinguished monoid is the set of shape
maps whose induced action on each source level is linear.

- M1: identity/composition are manifestly linear. A pointwise fusion limit
  inherits the linear action at source level `n` from its stage `n`.
- M3: for source level `n<m`, insert at target level `m` the coordinate
  projection `e(w)=w_n`. Above a descendant of the edge labelled `c`,
  the inserted value is exactly `c`.
- M2: contract the globally skipped level `t=lev(F(a))-1`. At the
  source level `n`, the resulting map into `F₂^t` is injective and
  linear. Its linear left inverse extends the original deleted coordinate
  to a linear functional on all of `F₂^t`. Reinserting this functional
  recovers `F` through source level `n`.

The Lean implementation is split into `BinaryWordTree`,
`LinearBoringInsertion`, `LinearBoringShapeMap`,
`BinarySkippedContraction`, `LinearBinaryContraction`,
`LinearBinaryM2`, `LinearBinaryDuplication`, and
`LinearBinarySMTree`. There were elaboration errors in
`LinearBinaryMonoidBasic.lean` in the last completed run; the latest
repair is not yet green and these claims are therefore not promoted to
validation markers.

## Combinatorial adversarial audit: are all subspaces reached?

A `d`-dimensional binary subspace admits a canonical coordinate
description. Scan ambient coordinate functionals from left to right on
the subspace. Mark a pivot whenever the current functional is not in
the span of earlier functionals. The `d` pivot functionals form a basis
of its dual. In the corresponding source coordinates, a pivot bit is
exactly the next free input bit; every non-pivot bit is a linear
combination of earlier pivots. Thus the intended exact successor
approximations should enumerate precisely the fixed-dimensional
subspaces, not basis-dependent copies.

`scripts/check_binary_successor_small.py` exhaustively checks this
claim for all `N≤5`: all subspaces of each dimension are reached. It
also checks for `N≤4` that every subspace `P` of a represented target
`W` has a row-echelon preimage, and for `N≤5` that a skipped
penultimate coordinate can be contracted and linearly reinserted.
These are **finite tests**, not formal proofs.

The factorisation proof in Lean should have two independent parts:

1. **Surjectivity of the range encoding.** Construct the greedy pivot
   representation of every `FixedSubspace d N` as an exact finite
   linear binary successor approximation.
2. **Composition of ranges.** For exact approximations `f,g`,
   prove the induced levelwise linear map is the composite of the
   maps induced by `f` and `g`. Then the range of `f∘g` is
   `f(range(g))`. A new theorem in
   `LinearBinaryComposition.lean` expresses this but awaits Lean checking.

For arbitrary `P≤range(f)`, pull `P` back along the injective
linear map induced by `f`. Apply (1) to obtain `g` representing
that preimage, and (2) to conclude that `f∘g` represents `P`.
Only then is the concrete `BinarySubspaceSuccessorEncoding`
constructed and the `BinarySubspaceRamsey` hypothesis eliminated.

## Manuscript boundary

The circulation text is frozen. BANANA PR #155 adds only validation
markers, one `\\todo` about the unfinished GLR bridge, and an updated
Lean commit pin. It does not rewrite existing prose. The unproved
encoding is deliberately marked as an interface, not as verified.

The remaining gap is independent of the established infinite-degree
half and of the coherent-EPPA package.
