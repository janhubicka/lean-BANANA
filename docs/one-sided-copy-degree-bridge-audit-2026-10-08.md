# Circulation degree-one copy/subspace bridge — staged audit (8 October 2026)

**Status: source staged, not kernel-checked.** GitHub Actions runners are
unavailable, and the isolated local environment does not contain Lean, Lake
or a Mathlib checkout. The code must not be cited as a green Lean validation
marker. The review below consists of two deliberately adversarial manual
checks by the authoring assistant, **not independently spawned referees**.

## Exact statement match

The circulation theorem is about Ramsey degrees of *unlabelled copies*,
not source embeddings. The existing binary-GLR interface in
`BinarySubspaceRamseyInterface.lean` talks about `FixedSubspace a n`
and proves `LeftOneSidedCopyRamseyOne` and its right analogue. Those
statements were not yet a formal consequence for the actual
`BananaMatrixStructure.copyRamseyDegreeLE` predicate.

The new `BananaCopySubspaces.lean` assigns to every copy its left and
right subspaces. The source-copy range on each sort is exactly the carrier
of the corresponding subspace. Both assignments commute with ambient
embeddings. When the other source sort is zero, its copy range is the
singleton zero vector, so the nonzero sort's subspace determines the
unlabelled copy uniquely.

`BananaOneSidedCopyDegree.lean` proves a candidate theorem in the
other direction: every fixed-dimensional subspace of an ambient perfect
pairing is the range of a one-sided source copy. A finite-dimensional
linear equivalence from the source sort to this subspace yields the
embedding; the other sort maps to zero and imposes no relation.
The choice of linear equivalence affects the *embedding* but not the
copy's range.

## Adversarial desk check A: copies, automorphisms and zero cases

* The subspace is recovered from the actual finite range, not from a
  distinguished source basis. Therefore source automorphisms do not
  change the colour assigned to a copy.
* Each two-sorted copy is determined by the pair of its ranges. For a
  left-only or right-only source, the missing range really is `{0}`
  in every ambient structure, including ambients of arbitrary bilinear
  pairing and arbitrary dimension on the other sort.
* The dimension-zero source is covered without exceptions: its two
  image ranges are both `{0}`. This avoids an unnecessary positivity
  condition.
* The finite-dimensional linear equivalence exists only because the
  subspace has *exactly* the source dimension. This is supplied by
  `FixedSubspace`, not assumed of arbitrary finite subsets.

## Adversarial desk check B: Ramsey quantifiers and degree zero

Fix a source `A : BananaMatrixStructure a 0`, a target `B` and a
positive finite number of colours. The one-sided theorem supplies a
standard perfect ambient `B_n` for *all* colourings of its
`a`-subspaces. Colour a subspace `W` by the colour of the
corresponding unlabelled `A`-copy. It gives an embedding `F:B→B_n`
and a single colour `c`.

For any unlabelled `A`-copy `D` of `B`, the subspace of `D.map F`
equals the image under `F.left` of the subspace of `D`. Both
`D.map F` and the chosen copy over that subspace have zero right
range; uniqueness therefore identifies them. Consequently their
actual *copy* colours equal `c`, as required by
`A.copyRamseyDegreeLE 1`. The right-only case is symmetric.

Degree zero is ruled out separately, without relying on GLR:
take `B=A` and one colour in the definition of degree at most zero.
The identity source copy survives every witness embedding, so the
set of used colours must be nonempty, contradicting cardinality zero.
Thus, once compiled, the two staged conjunctions establish exactly
degree one, including both-zero source.

**Result of desk reviews:** no mathematical counterexample found for
these finite-dimensional reductions. No claim is made that the Lean
source elaborates or has passed an independent external referee.

## Independent finite regression

`python3 scripts/check_one_sided_copy_subspaces.py` was executed
locally. Result:

* 231 injective source maps, including empty dimension;
* 24 distinct subspaces, exhaustively compared with all additive-closed
  subsets through ambient dimension three;
* 506 nested embedding/composition pairs;
* no counterexamples to subspace representability, choice
  independence or functoriality.

The calculation concerns finite models and cannot certify arbitrary
dimensions or Lean proof terms.

## Remaining mandatory verification

1. Provide a local Lean/Lake/Mathlib checkout matching `lean-toolchain`.
2. Run `lake env lean BANANA/NonPrecompact/BananaOneSidedDegreeAxiomAudit.lean`,
   inspect each printed axiom set, and run `lake build`.
3. Fix any elaboration or Mathlib API mismatches. Particularly scrutinise
   `LinearEquiv.ofFinrankEq`, the `Finset.mem_image` witnesses,
   `Submodule.ext`, `FixedSubspace.map`, and `Finset.card_pos`.
4. Separately build the outstanding `GLRAxiomAudit.lean` and the
   direct two-sided `BananaCopyDegreeAxiomAudit.lean`. New statements
   rely transitively on the successor-tree instance and do not bypass
   that obligation.
5. Arrange two genuinely independent adversarial referee checks of the
   mathematical proof and its Lean statement. Until then, this document
   remains an internal desk audit.
6. Only after successful kernel/axiom verification, import the new
   modules in root `BANANA.lean`, pin the verified commit in the
   circulation manuscript and promote the appropriate markers.
   Do not modify the frozen circulation prose.

The manuscript-side change associated with this branch is **validation
markers and an internal TODO only**, never a prose or proof rewrite.
