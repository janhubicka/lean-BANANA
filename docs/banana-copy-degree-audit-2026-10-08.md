# Direct BANANA copy-degree formalisation audit (8 October 2026)

Status: **staged Lean source, not kernel-verified**. The GitHub Actions
budget is exhausted, and no Lean/Lake compiler or Mathlib checkout is
available in the isolated local container. This audit is mathematical
and static; neither pass below is an independently spawned referee.

## Scope and new declarations

1. `BananaCopyRanges.lean` records a copy by its two image ranges.
   Equality is equality of unlabelled substructures, not equality of
   embeddings. The two sorts are separate and the ambient pairing
   determines the restriction once these ranges are fixed.
2. `BananaCopyPalette.lean` colours an unlabelled A-copy by the *set*
   of colours occurring on its internal four-element line-pair copies.
   The palette is independent of the embedding used to realise A.
   Its cardinal is bounded by
   `s = Fintype.card (BananaLinePairCopy A b)`.
3. `BananaCopyDegree.lean` states copy Ramsey degree using
   `BananaCopyRanges` throughout and proves an obstruction for
   all sources with nonzero left and right sorts. The proof uses
   `k = t*s`, hence `2^k > t*s` even when `t*s = 0`.
4. `BananaCopyDegreeAxiomAudit.lean` provides five transitive
   `#print axioms` checks, but these still require execution
   by Lean. No green manuscript markers may refer to these
   declarations before a successful kernel build.

## Adversarial pass A: copy semantics

* **The same copy may have many embeddings.** This is handled by
  quotienting only *the data*, not constructing an explicit quotient:
  the two finite image sets are the actual copy. The image of a
  copy under an ambient embedding is obtained functorially by
  `Finset.image` on both sorts.
* **Line pairs inside a copy might depend on a chosen basis.**
  They do not. A pair is internal precisely when its nonzero left
  and right vectors belong to the two image sets and have pairing
  value b. The preimage lemma uses the injectivity of the two
  coordinate maps and pairing preservation to recover a unique
  source pair.
* **A source may admit automorphisms.** The palette records every
  line-pair residue present, so reparametrising the same copy
  changes neither the pair set nor the palette. No rigidity of A
  is invoked (only rigidity of the original four-element A_b).
* **Zero sorts and zero pairing.** The two-sided conclusion requires
  positive dimensions, not nondegeneracy. A zero pairing with
  nonzero sorts still contains A_0; the one-sided case is handled
  separately by binary GLR.

## Adversarial pass B: quantifiers, palette size and forcing

Fix a source A with a selected line-pair embedding
`i : A_b -> A` and a purported degree bound t. Set
`s = |copies(A_b,A)|`, `k = t*s` and
`q = 2^(k+1)`. Given the perfect target
`B_n`, `n = dim L_A + dim R_A + q`, assume the copy
Ramsey-degree property returns ambient C. Fix the completion
residue colouring of A_b copies in C from the previously
formalised persistent-colouring theorem.

* **The colour set is finite.** Every A-copy is coloured by a
  subset of `Fin (2^k)`; this type has finite cardinal and
  can be encoded as an ordinary finite colour type via
  `Fintype.equivFin`.
* **A palette contains at most s colours.** Its elements are
  images of line pairs contained in A, independently of the
  chosen representation of the copy.
* **The selected perfect target forces every residue.** Embed
  `B_q` in `B_n`, then let the Ramsey property select
  `f : B_n -> C`. For each of the `2^k` residue colours,
  persistent colouring gives a line pair in `f(B_q)`.
  The line-pair extension theorem yields an A-copy in
  `B_n` containing its preimage. The palette of that A-copy
  in C therefore contains the selected residue colour.
* **Counting contradiction.** At most t distinct A-copy
  palette colours in `f(B_n)` means that the union of their
  sets contains at most `t*s` residue colours. But every
  element of `Fin (2^k)` is in that union, contradicting
  `t*s < 2^k`. Extra palette colours in a witness set are
  avoided by taking the *image* of actual A-copy palettes
  before applying the union estimate.

**Conclusion of mathematical audit:** these two independently
constructed checks of different obligations revealed no remaining
logical gap in the direct copy-degree argument. This is a claim about
the mathematical reduction only, **not** a kernel check or independent
referee certification.

## Independent finite regression

`scripts/check_copy_palettes_small.py` compares the source-embedding
and intrinsic range presentations. Locally it passed on 29,768
injective pairing-preserving embeddings grouped into 7,750
unlabelled range copies, checking 15,500 source/pairing cases
and 178,608 equality/bound comparisons. Ambient dimensions
are at most 3 on each sort: all pairings were enumerated
for dimensions at most 2 and eight deterministic matrices per
larger dimension were checked.

This confirms the representative-independence and palette-size
claims in small models, but **does not** prove the universal theorem.

## Remaining Lean build work

1. Run `lake env lean BANANA/NonPrecompact/BananaCopyDegreeAxiomAudit.lean`
   on a local checkout with installed Lean/Lake and Mathlib.
2. Address elaboration or API issues, particularly `Fintype` instances,
   `Finset.image_image`, the image-subspace equality,
   `Finset.card_biUnion_le`, and `Equiv.symm_apply_apply`.
3. Inspect all five printed axiom sets for `sorryAx` or extra axioms.
4. Only then import the new modules into root `BANANA.lean`,
   add a pinned green validation marker at the circulation
   degree-classification theorem, and remove/resolve its obsolete
   TODO **without modifying the frozen prose**.
5. The one-sided case already follows from the merged binary GLR
   work, but a direct identification between the `BananaCopyRanges`
   degree-one formulation and the older fixed-subspace interface
   should also be kernel-checked before claiming that the whole
   theorem is formalised.

No existing circulation sentence, theorem statement or proof was
modified by this branch.
