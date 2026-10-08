import BANANA.NonPrecompact.LinePairSourceEmbedding

/-!
# Four-element BANANA copies as structural embeddings

A nonzero pair of vectors of pairing value `b` is not merely a convenient
encoding: it comes from an embedding of the one-dimensional two-sorted
source `linePairSource b`. Conversely, every such embedding determines
the pair of images of the two basis vectors.

The resulting transfer proves infinite Ramsey degree for colourings of
actual source embeddings, using the already established persistent
colourings of line pairs. It requires no choice of representatives and
does not assume an abstract degree-propagation theorem.
-/

namespace SuccessorTree.NonPrecompact

/-- The nonzero generator of the one-dimensional binary coordinate space. -/
private def linePairBasis : Fin 1 → F2 :=
  Pi.single (0 : Fin 1) 1

private theorem linePairBasis_ne_zero : linePairBasis ≠ 0 := by
  intro h
  have h0 : (1 : F2) = 0 := by
    simpa [linePairBasis] using congrFun h (0 : Fin 1)
  exact one_ne_zero h0

/-- An embedding of the four-element source gives a line-pair copy by
taking the images of its unique nonzero basis vectors. -/
def BananaMatrixEmbedding.toLinePairCopy
    {l r : ℕ} {A : BananaMatrixStructure l r} {b : F2}
    (e : BananaMatrixEmbedding (linePairSource b) A) :
    BananaLinePairCopy A b where
  left := e.left linePairBasis
  right := e.right linePairBasis
  left_ne_zero := by
    intro h
    apply linePairBasis_ne_zero
    apply e.left_injective
    simpa using h
  right_ne_zero := by
    intro h
    apply linePairBasis_ne_zero
    apply e.right_injective
    simpa using h
  pairing := by
    calc
      A.eval (e.left linePairBasis) (e.right linePairBasis) =
          (linePairSource b).eval linePairBasis linePairBasis :=
        e.pairing_apply _ _
      _ = b := by simp [linePairBasis, linePairSource_eval]

/-- Equality of line-pair copies needs only equality of their two vectors:
nonzeroness and pairing preservation are propositions. -/
theorem BananaLinePairCopy.eq_of_vectors
    {l r : ℕ} {A : BananaMatrixStructure l r} {b : F2}
    (P Q : BananaLinePairCopy A b)
    (hleft : P.left = Q.left) (hright : P.right = Q.right) :
    P = Q := by
  cases P with
  | mk x y hx hy hp =>
    cases Q with
    | mk x' y' hx' hy' hp' =>
      cases hleft
      cases hright
      rfl

/-- Passing from a line-pair copy to its structural embedding and back
recovers the original copy. -/
@[simp] theorem BananaLinePairCopy.toSourceEmbedding_toLinePairCopy
    {l r : ℕ} {A : BananaMatrixStructure l r} {b : F2}
    (P : BananaLinePairCopy A b) :
    P.toSourceEmbedding.toLinePairCopy = P := by
  apply BananaLinePairCopy.eq_of_vectors
  · exact P.toSourceEmbedding_left_basis
  · exact P.toSourceEmbedding_right_basis

/-- Extracting source basis images commutes with postcomposition. -/
theorem BananaMatrixEmbedding.toLinePairCopy_comp
    {l r l' r' : ℕ}
    {A : BananaMatrixStructure l r}
    {B : BananaMatrixStructure l' r'}
    {b : F2}
    (f : BananaMatrixEmbedding A B)
    (e : BananaMatrixEmbedding (linePairSource b) A) :
    (BananaMatrixEmbedding.comp f e).toLinePairCopy =
      f.mapLinePairCopy e.toLinePairCopy := by
  apply BananaLinePairCopy.eq_of_vectors
  · rfl
  · rfl

/-- The source embedding determined by a pair remains compatible with
the pair's image under every BANANA embedding. -/
@[simp] theorem BananaMatrixEmbedding.toLinePairCopy_comp_toSource
    {l r l' r' : ℕ}
    {A : BananaMatrixStructure l r}
    {B : BananaMatrixStructure l' r'}
    {b : F2}
    (f : BananaMatrixEmbedding A B)
    (P : BananaLinePairCopy A b) :
    (BananaMatrixEmbedding.comp f P.toSourceEmbedding).toLinePairCopy =
      f.mapLinePairCopy P := by
  rw [BananaMatrixEmbedding.toLinePairCopy_comp,
      P.toSourceEmbedding_toLinePairCopy]

/-- The genuine embedding-colouring Ramsey-degree bound for the rigid
four-element source `linePairSource b`. For these sources, embeddings
and copies agree, because there are no nontrivial source automorphisms. -/
def linePairEmbeddingRamseyDegreeLE (b : F2) (t : ℕ) : Prop :=
  ∀ (lB rB : ℕ) (B : BananaMatrixStructure lB rB)
      (numColours : ℕ), 0 < numColours →
    ∃ (lC rC : ℕ) (C : BananaMatrixStructure lC rC),
      ∀ colouring :
          BananaMatrixEmbedding (linePairSource b) C → Fin numColours,
        ∃ f : BananaMatrixEmbedding B C,
          ∃ colours : Finset (Fin numColours),
            colours.card ≤ t ∧
            ∀ e : BananaMatrixEmbedding (linePairSource b) B,
              colouring (BananaMatrixEmbedding.comp f e) ∈ colours

/-- Any finite degree bound for structural source embeddings would give
the same bound for the line-pair copies used in the colouring proof. -/
theorem linePairCopyRamseyDegreeLE_of_embeddingDegreeLE
    {b : F2} {t : ℕ}
    (h : linePairEmbeddingRamseyDegreeLE b t) :
    linePairCopyRamseyDegreeLE b t := by
  intro lB rB B numColours hnum
  obtain ⟨lC, rC, C, hC⟩ := h lB rB B numColours hnum
  refine ⟨lC, rC, C, ?_⟩
  intro colouring
  let embeddingColour :
      BananaMatrixEmbedding (linePairSource b) C → Fin numColours :=
    fun e => colouring e.toLinePairCopy
  obtain ⟨f, colours, hcard, hmono⟩ := hC embeddingColour
  refine ⟨f, colours, hcard, ?_⟩
  intro P
  simpa only [embeddingColour,
      BananaMatrixEmbedding.toLinePairCopy_comp_toSource] using
    hmono P.toSourceEmbedding

/-- Both rigid four-element BANANA structures have infinite Ramsey degree
in the ordinary structural-embedding formulation. -/
theorem linePairEmbeddingRamseyDegree_infinite (b : F2) :
    ∀ t : ℕ, ¬ linePairEmbeddingRamseyDegreeLE b t := by
  intro t h
  exact (linePairCopyRamseyDegree_infinite b t)
    (linePairCopyRamseyDegreeLE_of_embeddingDegreeLE h)

end SuccessorTree.NonPrecompact
