# Two-sided BANANA degree formalisation: adversarial desk audit

Status: **uncompiled draft**. The code in this branch has not passed a local
Lean kernel build or an axiom audit. No GitHub Actions or remote runners
were used. The points below are manual proof checks, **not independently
spawned referee reports**.

## Scope and statement audit

* `LinePairEmbeddingDegree` identifies the four-element rigid source
  `linePairSource b` with a pair of nonzero vectors of pairing value `b`.
  The degree theorem concerns structural embeddings, not arbitrary
  labels on ordered pairs.
* `LinePairExtension` extends an arbitrary **prescribed embedding**
  of this four-element source into a perfect target. It uses the finite
  completion of the ambient source, then the homogeneity theorem to
  transport the embedded line pair.
* `BananaEmbeddingDegree` colours each **embedding** of a general
  source `A` by restricting it to one chosen line pair. An A-copy
  need not have a unique chosen line pair when A has automorphisms.
  The theorem therefore explicitly concludes infinite **embedding**
  Ramsey degree, **not** infinite copy Ramsey degree.

## Adversarial checks of the mathematical reduction

1. **Can the perfect target contain every prescribed line pair?**
   In the proof the large target has dimension
   `n = (l + r) + q`, where `l,r` are the dimensions of A and
   `q = 2^(k+1)`. A copy of `B_q` embeds into `B_n`, so
   the persistent line-pair colouring is still witnessed on that
   subblock. A prescribed line-pair copy in `B_n` extends to A
   by first completing A into `B_(l+r)` and conjugating the copy
   via homogeneity of `B_n`.
2. **Does this transfer all colours to embeddings of A?** For each
   residue colour in the fixed completion of C, persistence gives
   a line-pair in the copy of `B_q`. Mapping it into `B_n` and
   extending to A produces an embedding e of A into `B_n`.
   Thus the same colour occurs on the composite `f ∘ e` for
   any distinguished target embedding `f : B_n → C`.
3. **Can one conclude the manuscript's copy-degree classification?**
   **Not yet.** An embedding-colouring can distinguish different
   parametrisations of the same substructure. To transfer to
   unlabelled copies one must use the finite automorphism group
   and the copy Ramsey-degree propagation lemma (or formalise the
   quotient of embeddings by source automorphisms). This is the
   separate obligation recorded by the manuscript TODO.
4. **Corner cases.** The positive-dimensional hypothesis is
   indispensable: a zero-dimensional sort has no nonzero line
   pair and is covered by the separate one-sided GLR theorem.
   Both pairing values `b = 0` and `b = 1` are covered by the
   full `B_q` affine-slice persistence lemma; the sharper
   `B_(q-1)` lemma is only needed for `b = 1`.

## Pending machine checks

* Run `lake build` locally and resolve elaboration issues.
* Run `lake env lean BANANA/NonPrecompact/LinePairDegreeAxiomAudit.lean`
  or build the imported module; inspect **all four**
  `#print axioms` outputs for `sorryAx` and extra axioms.
* Confirm `linePairBasis` and `Pi.single` reduce as expected;
  confirm the finite-dimensional addition rewrite in `j`.
* Review the exact theorem statements against the circulation
  manuscript. Only then add any **new** green verification markers.
* Request independent adversarial refereeing when an actual
  independent reviewer capability is available.

The associated manuscript patch touches no circulation prose and
remains independent of this uncompiled Lean work.

## Exhaustive finite regression (8 October 2026)

`scripts/check_linepair_extension_small.py` was run locally with Python.
It exhaustively enumerates injective left and right coordinate maps,
all pairing matrices, all nonzero source vector pairs, and all
compatible prescribed image pairs in the perfect target for ten
dimension triples `(l,r,extra)` with `l+r+extra <= 4`.
Result: **126,871 pairs of coordinate embeddings examined, 310
source-pair coverage equalities checked, no counterexample**.
This is regression evidence for the extension lemma, not a Lean proof
or a kernel check.

## More direct route to the manuscript's copy-degree classification

The manuscript states degrees of *unlabelled copies*. It is possible
to avoid choosing representatives of those copies, and even to avoid
importing the abstract degree-propagation theorem, using set-valued
colours. Let `A` contain a fixed line-pair source `P = A_b`, and
let `s` be the number of P-copies within A (finite, positive).

For each ambient C choose the fixed-completion colouring
`c : copies(P,C) -> Fin (2^k)` from the persistent-colouring theorem.
Colour each unlabelled A-copy `D` by the **set** of c-colours of the
P-copies contained in D. This is independent of a labelling of D.
Every such set has cardinal at most `s`. In a distinguished perfect
target of dimension `n = dim(L_A) + dim(R_A) + 2^(k+1)`, every P-copy
extends to an A-copy by the line-pair extension lemma, and the P-copy
colours cover all `2^k` values. If only `t` distinct set-colours
occurred among its A-copies, their union could have cardinal at most
`s*t`. Choosing `k` with `2^k > s*t` is a contradiction.

This gives the desired *copy* Ramsey-degree obstruction without
a source-automorphism quotient or a general amalgamation-class
degree-propagation theorem. It remains to implement the copy-range
representation and finite set-counting argument in Lean and run a
kernel/axiom audit before adding a green marker.

## Safe integration policy

The new modules are **not imported by root `BANANA.lean`** pending
a successful local kernel build. To check them, run
`lake env lean BANANA/NonPrecompact/LinePairDegreeAxiomAudit.lean`
or the corresponding targeted Lake build, then restore the imports
only after a clean result. Merging the staged source files is not
a claim that the new declarations have been accepted by the kernel.
