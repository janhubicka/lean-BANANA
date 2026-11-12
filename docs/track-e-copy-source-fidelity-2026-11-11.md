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
4. `copyRanges_precompose`: explicit invariance of the image sets
   after precomposing an embedding with the source isomorphism.
5. `copyRangesAmbientEquiv`: equivalence of unlabelled copy types
   after **ambient** changes of coordinate bases.
6. `copyRamseyDegreeLE_iff`: invariance of every finite copy
   Ramsey-degree bound under source-coordinate changes.
7. `copyRamseyDegree_classification_transport`: the terminal
   finite-matrix classification transported through an arbitrary
   source pairing isomorphism. The source and ambient transports are
   separate to avoid silently equating parametrised embeddings
   and unlabelled copies.

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

For an ambient pairing isomorphism `j:B→B'`, mapping each source
copy range `(U,V)` to `(j_L(U),j_R(V))` is a bijection;
its inverse uses `j⁻¹`. Source and ambient transports commute with
composition because they operate on the same two underlying image
subspaces. Thus **both** ends of a copy in the matrix category are
coordinate-independent; this is not merely preservation of source
automorphism orbits.

For an abstract finite bilinear pairing, choose finite bases of both
sorts and form the matrix of cross-pairings. This gives an isomorphic
coordinate pairing. Every abstract embedding is represented by a pair
of injective linear maps preserving the pairing, and a copy is
completely determined by its two vector-subspace images. The proposed
new result is a **source-coordinate invariance component**, not yet
a formal Lean equivalence for a separately defined category of
abstract finite pairings. That last packaging remains to be done.

## Exact transfer to the abstract finite pairing class (desk proof)

Let `K_abs` consist of arbitrary finite-dimensional vector-space pairs
over F₂, each equipped with an arbitrary bilinear pairing; let `K_mat`
consist of the matrix presentations in `BananaMatrixStructure`.
Forgetful interpretation of the standard coordinate spaces defines a
functor `U:K_mat→K_abs`.

1. **Essential surjectivity.** For any `A∈K_abs`, choose bases of
   its two vector spaces. Evaluating its pairing on those bases gives
   a rectangular matrix `A₀∈K_mat`. The two basis maps form an
   original-language isomorphism `α:U(A₀)≅A`. This also covers
   zero-dimensional sorts and degenerate pairings.
2. **Fully faithful on embeddings.** Once source and target bases are
   fixed, any pair of linear maps is represented by its coordinate
   matrices. The maps are injective and preserve the pairing in
   `K_abs` exactly when they satisfy the two injectivity fields and
   `pairing_apply` in `BananaMatrixEmbedding`. Conversely, every
   such Lean matrix embedding is an abstract-language embedding.
3. **Unlabelled-copy fidelity.** A copy is the pair of image
   subspaces with its pairing inherited from the ambient object.
   Source automorphisms do not produce distinct copies. The staged
   `copyRangesEquiv` preserves the actual ambient image sets;
   `copyRangesAmbientEquiv` transports those sets by the ambient
   coordinate isomorphism.
4. **Ramsey quantifiers.** Assume the matrix statement
   `A₀.copyRamseyDegreeLE t`. Fix arbitrary `B∈K_abs` and
   `r≥1`; choose coordinates `B₀≅B`, then apply the matrix
   statement to the **already chosen** `B₀,r` to obtain `C₀`.
   Use `U(C₀)` as the abstract witness. For every colouring of
   `A`-copies in it, pull back along `α`, apply the matrix
   statement to find `f₀:B₀→C₀`, then postcompose
   `f₀` with the inverse coordinate isomorphism `B→B₀`.
   Naturality shows that the same set of at most `t` colours
   occurs on the `A`-copies inside this image. Crucially, the
   witness `C₀` was selected **before** the colouring.
5. **Reverse implication.** If the abstract statement holds,
   apply it to the underlying abstract source and any matrix target
   `B₀`; choose coordinate bases on the abstract witness `C`.
   Transport arbitrary copy colourings and the resulting embedding
   across this ambient isomorphism. This produces a matrix witness
   for `A₀,B₀,r`.

This proves equality of the abstract and matrix copy-degree
predicates, including the lack of any finite bound. The argument
does **not** rely on rigid sources, canonical bases, nondegeneracy,
or an unproved Ramsey theorem. Its only mathematical inputs beyond
the staged Lean components are elementary finite-dimensional
linear algebra and the equivalence of finite pairings with their
coordinate matrices.

**Formalisation boundary:** the abstract class `K_abs` has not been
declared as an independent Lean category, and Steps 1–5 above are
not yet a Lean theorem. The finite-matrix theorem on `main` was
previously kernel-checked; the staged coordinate transport must pass
its own local Lean checks before being counted as formal evidence.

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

### Adversarial type-level correction (12 November)

The first staged statement of `copyRanges_precompose` mistakenly
asserted an equality between `BananaCopyRanges A C` and
`BananaCopyRanges A' C`. These are **different Lean types** when
`A` and `A'` are distinct source indices, even though the copy
ranges are identical. This was detected by an independent typing
review before any kernel-verification claim. The statement was
repaired to assert equality **after projecting to the common pair
of ambient image sets** via `.1`. The separate
`copyRangesEquiv` is the correctly typed equivalence between the
two source-indexed copy types.

This is not a counterexample to the mathematical source-invariance
claim, but it is a concrete reason why an uncompiled Lean script
must not be labelled validated. The amended declaration still
requires a local Lean elaboration and axiom check.

## Locally executed independent regression

Run:

```sh
python3 scripts/test_track_e_copy_fidelity.py
```

The extended Python regression passed locally on **12 November 2026**:

| Finite test family | Checks |
| --- | ---: |
| All pairing matrices with each sort of dimension at most 2 | 31 structures |
| All ordered source/ambient pairs | 961 |
| Source changes of bases | 641 |
| Source-isomorphism copy-set equalities across ambients | 19,871 |
| Direct verification of pairing preservation under basis changes | 9,661 |
| Individual source-embedding precomposition witnesses | 26,333 |
| Ambient changes of bases | 641 |
| Ambient isomorphism bijections on entire source-copy sets | 19,871 |
| Independent **rank-characterisation** copy-set oracle | 961 |
| One-sided copy/subspace identifications | 155 |
| Palette cardinality checks | 1,522 |
| Explicit embedding-composition checks | 991 |

Every possible pairing matrix of those dimensions was included,
including degenerate matrices, empty sorts, and the zero pairing.
The palette regression used an arbitrary seven-colour ambient function,
not a source-parametrised colouring. In particular, the **independent
rank oracle** enumerates *pairs of subspaces*, independently of the
embedding enumeration, and accepts them as copies exactly when the
restricted binary bilinear form has the same matrix rank as the
source. This criterion is sound since rectangular bilinear forms over
a field are classified, under independent changes of bases on the
two sorts, by their rank. The oracle agrees with the embedding-range
implementation in every one of the 961 finite source/ambient pairs.
This adversarial cross-check does not establish the general theorem,
nor does it imply a Lean kernel proof.

## Verification gate and remaining work

**UNCOMPILED DRAFT: DO NOT MERGE OR UPGRADE VALIDATION MARKERS.**
The local runtime has no Lean/Lake installation or cached toolchain
(rechecked 12 November 2026), and it cannot resolve github.com to
download one. GitHub Actions are out of budget, so no CI check is
used as a substitute. The previously verified 8 November offline
compiler/mathlib bundle was hosted as short-lived GitHub Actions
artifacts; its successful workflow now returns no downloadable
artifacts, so the older bundle cannot be restored in this runtime.

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
