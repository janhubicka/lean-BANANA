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


## Update — 7 October: one remaining representation theorem

The exact-coordinate class is nonempty for every source dimension `a` and
target terminal dimension `D ≥ a`, witnessed by repeated zero linear
coordinate insertions in `LinearBinaryExactCoordinates.lean`. The range
of exact finite composition is the image of the inner range under the
outer induced linear map in `LinearBinaryComposition.lean`.

The new `LinearBinaryRangeTransfer.lean` replaces the earlier
`BinarySubspaceSuccessorEncoding.factor` requirement by the single
proposition `EveryBinarySubspaceRepresentable`: every `d`-subspace of
`F₂^N` is the range of an exact linear binary successor approximation
with source width `d+1` and terminal level `N`.

**Reduction proof.** Given an exact outer map with injective linear
action `φ:F₂^D→F₂^N` and an `a`-subspace `P≤range φ`, put
`Q=P.comap φ`. The standard Mathlib identity
`Submodule.map_comap_eq_of_le` gives `φ(Q)=P`.
`Submodule.equivMapOfInjective` shows `dim Q=dim P=a`.
Representability supplies an exact coordinate map `g` with range `Q`.
The composition lemma then says the range of the exact composite with
the outer approximation is `φ(Q)=P`. Thus the independent
factorisation field is redundant.

The dimension-zero and full-dimensional instances of range
representability are separately formalised by `zeroPaddingExact`
and subspace dimension uniqueness. The genuine remaining case is
`0<d<N`.

**Greedy pivot proof to formalise.** Let `X≤F₂^N` and, for each
`j<N`, let `λ_j:X→F₂` be restriction of evaluation at coordinate
`j`. Scan `j=0,…,N-1`. Select `j` as a pivot precisely when
`λ_j` does not lie in the span of `λ_i`, `i<j`. The selected
functionals form a basis of `X*` because all ambient evaluations
separate points of `X`; hence their number is `dim X=d`.
In the associated dual coordinates `X≅F₂^d`, each pivot is exactly
the next free input bit and each nonpivot is a linear combination
of preceding pivot coordinates. Insert the nonpivot target coordinates
in increasing order as the corresponding linear boring extensions.
Their composition is a member of the levelwise-linear monoid,
takes source level `d` to terminal level `N`, and has range `X`.

For a more local induction one can split the last ambient coordinate.
`BinarySubspaceStep.lean` states and proves the basic alternative:
for `P≤V×F₂`, either the first-coordinate projection is injective on
`P`, or `P=π(P)×F₂`. These are precisely the dependent-coordinate
and new-pivot cases. The remaining formal task is to connect that
local dichotomy with the recursive construction of the global
successor approximation.

The independent finite audit now checks uniqueness and completeness of
the pivot codes against the Gaussian-binomial subspace counts through
ambient dimension seven; it checks composition through dimension five.
These computations are independent tests and **not** Lean certification.

The latest new Lean declarations are on a draft branch and **must not
be reported as kernel-verified until the corresponding Lean build
and axiom checks succeed**. The circulated manuscript remains
unchanged except for separately approved TODOs and validation markers.


## Canonical-extension simplification of the pivot case

The established successor library already provides
`SMTree.canonicalExtension` and
`canonicalExtension_level_succ`: after a protected finite source prefix
through level `d`, all subsequent target image levels are consecutive.

For the bit-labelled binary prefix tree, that immediately gives the
identity
`canonicalExtension_appendBit_at_cut`:
if a source word `w` has length `d`, then
`G(w⌢c)=F(w)⌢c` for the canonical extension `G` of `F`
through level `d`. Its proof combines exact next-level behaviour with
weak successor preservation; the latter becomes exact because there is
no extra target level available between the two image levels.

Therefore, if an exact finite approximation of width `d+1` ends at
level `N`, its canonical extension through level `d` gives an exact
approximation of width `d+2` ending at `N+1`.
The new `LinearBinaryCanonicalPivot.lean` formalises these two
statements, conditional on successful Lean elaboration.

This closes the **construction** part of the independent-coordinate
case in the final-coordinate induction. The remaining API work is to
transport the range of the new levelwise linear map under
`lastCoordinateLinearEquiv` and prove it equals the old range
times `F₂`. The dependent-coordinate case instead uses the global
linear functional from
`BinarySubspaceStep.exists_linear_last_coordinate_of_injective`
and composes one boring-coordinate insertion at target position `N`.

This avoids an unnecessary global row-echelon matrix formalisation:
induct directly on the ambient coordinate length, using the two
local alternatives and the existing shape-map operations.


## Update — 8 October: complete induction submitted for compilation

The branch now includes
`LinearBinaryBoringExtension.lean` and
`LinearBinaryRepresentability.lean`, and its root module imports both.
The intended Lean statement `everyBinarySubspaceRepresentable` is
**unconditional** in source: no unproved hypothesis is supplied to the
representation theorem.

The dependent-coordinate branch factors through an exact approximation
whose level-`N` action inserts `e(x)` as the final coordinate. This
uses the existing `exactSubspace_comp` theorem and the identity
`Fin.insertNth_last'`, making the resulting range exactly the graph
of `e` over the preceding range.

The independent-coordinate branch uses
`canonicalExtension_appendBit_at_cut`, an instance of the existing
`SMTree.succ_eq_of_consecutive_levels`, to obtain
`F'(x,c)=(F(x),c)`. The associated subspace range is contained in
the pullback of `range F × F₂`. Both subspaces have dimension `d+1`,
so `Submodule.eq_of_le_of_finrank_eq` gives equality. This route needs
no converse-surjectivity argument.

The ambient-dimension induction uses the dichotomy of
`BinarySubspaceStep`. It proves the zero-dimensional base case,
projects each `P ≤ F₂^(N+1)` to `Q ≤ F₂^N`, applies induction to
`Q`, and chooses one of the two exact extensions. It also exposes
the intended unconditional conclusions
`binarySubspaceRamsey_via_successors` and
`leftOneSidedCopyRamseyOne_via_successors` /
`rightOneSidedCopyRamseyOne_via_successors`.

**Verification status.** These are source-level proof attempts, not
Lean-certified theorems: the current GitHub Actions run is queued due to
the runner situation and the available local container has no Lean
toolchain. Do **not** promote corresponding manuscript interface markers
to verified, pin these declarations as checked, or merge draft PR #7
until the actual kernel build and axiom audit succeed.

**Independent mathematical check.** The branch's
`scripts/check_binary_successor_small.py` now includes
`check_inductive_range_rebuilding`. A separately executed exhaustive
test of that exact reconstruction algorithm passed all 29,212 subspaces
of `F₂^7`, also checking all smaller ambient dimensions. This is finite
evidence only; it cannot replace the induction in Lean.

### Adversarial obligations before merge

1. Compile the whole dependency chain, starting with
   `LinearBinaryMonoidBasic.levelEquiv_insertLinearCoordinate`.
   Its dependent-list-index proof was still failing in the most recent
   completed CI log. No later file can be trusted while this blocker
   remains.
2. Verify that `toAM_representative_agrees` is used with the correct
   source cutoff in the two exact extensions, especially dimensions zero
   and one.
3. Verify that the last-coordinate membership transport reflects the
   submodule predicate in the reverse direction and that the induction
   handles `d=0` in the pivot branch by contradiction.
4. Run `lake build BANANA` and `#print axioms` on the final GLR and
   one-sided copy Ramsey declarations, ideally from a fresh local
   dependency cache, before updating `validation.tex`.
5. Keep circulation prose frozen. Only TODOs or justified validation
   markers may be added to the circulated TeX.
