# Track E: source-isomorphism fidelity of BANANA copy degrees (11 November 2026)

## Scope and boundary

The circulation manuscript is frozen. This branch changes **only** Lean
development, a local finite regression and this internal audit note. No
TeX proof, mathematical prose, validation mark or previously removed TODO
has been touched.

The merged classification
`BananaMatrixStructure.copyRamseyDegree_classification` proves the
finite-coordinate statement using **unlabelled copies**, identified by
the two image sets of a pairing-preserving source embedding. The
manuscript quantifies over arbitrary finite two-sorted binary vector
spaces with bilinear pairing. Choosing bases gives the matrix
presentation; verifying that the choice does not affect copy degrees is
the source-coordinate fidelity obligation isolated here.

## New formal target

`BANANA/NonPrecompact/BananaCopySourceIso.lean` stages:

1. `BananaCopySourceIso`: linear equivalences on the two sorts,
   preserving the bilinear pairing.
2. `copyRangesEquiv`: a bijection on actual unlabelled copies of the
   two source presentations into **every** ambient matrix pairing,
   preserving the same pair of underlying image sets.
3. `copyRangesEquiv_map`: naturality with respect to ambient
   embeddings.
4. `copyRamseyDegreeLE_iff`: invariance of every finite copy
   Ramsey-degree bound under source-coordinate changes.

Mathematically, let `i=(i_L,i_R):A→A'` be a pairing-preserving
isomorphism. If `e:A→C` is an embedding, then
`e∘i⁻¹:A'→C` has exactly the same left and right images as `e`.
Conversely, precomposing an `A'`-embedding with `i` preserves its
images. Thus the two source copy types consist of the same pairs of
ambient subspaces, with the same induced pairing. For an ambient
embedding `f:B→C`, both choices of source map send a pair `(U,V)`
to `(f_L(U),f_R(V))`, proving naturality. Given a colouring of
`A'`-copies in a degree witness, pull it back through this bijection,
apply the degree bound for `A`, then use naturality to recover the
same palette inside the selected `B`-copy. Apply the inverse
isomorphism for the converse.

For an abstract finite bilinear pairing, choose finite bases of both
sorts and form the matrix of cross-pairings. This gives an isomorphic
coordinate pairing. Every abstract embedding is represented by a pair
of injective linear maps preserving the pairing, and a copy is
completely determined by its two vector-subspace images. The proposed
new result is a **source-coordinate invariance component**, not yet
a formal Lean equivalence for a separately defined category of
abstract finite pairings. That last packaging remains to be done.

## Independent adversarial desk checks

- **Semantic check:** colouring embeddings instead of ranges would be
  inadequate for the manuscript. The implementation explicitly uses
  `BananaCopyRanges`, so source automorphism choices are invisible.
  Reparametrisation preserves the exact finite image sets.
- **Quantifier check:** source-isomorphism transport must be uniform
  in every finite target `B`, positive number of colours and every
  ambient colouring, *before* the witness embedding is selected. The
  staged implication follows that order. The degree-zero case remains
  excluded by the merged identity-copy theorem.
- **Two-sided check:** the existing infinite-degree theorem uses
  `s`, the number of line-pair subcopies of the source, and colours a
  whole source copy by its line-pair colour palette. The bound
  `|palette|≤s`, together with extension of forced line pairs, implies
  `2^k≤ts`; choosing `k=ts` contradicts `ts<2^k`. This does not
  assume source rigidity or nondegeneracy of its pairing.
- **Presentation check:** the manuscript's green check at
  `persistent-colouring.tex`, Theorem
  `thm:banana-degree-classification`, is currently at the correct
  declaration line (157); the other checked line pointers for
  line-pair existence (49), source embedding (71), and the two-sided
  theorem (170) also match the default-branch files. No obsolete
  marker was changed.

These are separate proof-obligation desk checks, **not** independent
human/agent referee certifications.

## Locally executed independent regression

Run:

```sh
python3 scripts/test_track_e_copy_fidelity.py
```

On 11 November 2026 the independent Python execution passed:

| Finite test family | Checks |
| --- | ---: |
| All pairings with each sort of dimension at most 2 | 31 structures |
| All ordered source/ambient pairs | 961 |
| Source changes of bases | 641 |
| Source-isomorphism copy-set equalities across ambients | 19,871 |
| One-sided copy/subspace identifications | 155 |
| Palette cardinality checks | 1,522 |
| Explicit embedding-composition checks | 991 |

Every possible pairing matrix of those dimensions was included,
including degenerate matrices, empty sorts, and the zero pairing.
The palette regression used an arbitrary seven-colour ambient function,
not a source-parametrised colouring. These tests are useful for
finding copy/embedding mix-ups; they do not establish the general
theorem.

## Verification gate and remaining work

**UNCOMPILED DRAFT: DO NOT MERGE OR UPGRADE VALIDATION MARKERS.**
The local runtime has no Lean/Lake installation or cached toolchain
(checked 11 November 2026), and it cannot resolve github.com to
download one. GitHub Actions are out of budget, so no CI check is
used as a substitute.

With a local checkout and the pinned `lean-toolchain` available:

```sh
lake env lean BANANA/NonPrecompact/BananaCopySourceIso.lean
lake env lean BANANA/NonPrecompact/BananaCopySourceIsoAxiomAudit.lean
python3 scripts/test_track_e_copy_fidelity.py
bash scripts/audit_all_axioms_local.sh
```

Referee tasks after compilation:
(i) inspect `ranges_comp_sourceIso` elaboration and pair-transport
orientation; (ii) check the transitive axioms of
`copyRamseyDegreeLE_iff` have only foundational dependencies; (iii)
package the chosen-bases equivalence for the actual abstract
finite-vector-space pairing category; (iv) only then consider a
new exact validation marker in the frozen manuscript. Do not reinsert
a TODO previously removed by Sofia.
