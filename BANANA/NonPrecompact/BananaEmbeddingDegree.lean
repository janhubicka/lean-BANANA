import BANANA.NonPrecompact.LinePairExtension

/-!
# Infinite embedding Ramsey degrees of two-sided BANANA structures

The fixed-completion colouring obstructs not just the rigid four-element
sources, but embeddings of every finite BANANA structure with nonzero
left and right sorts. Choose a four-element substructure of the source
and colour each embedding by the induced line-pair colour.

For each prescribed line-pair copy in a sufficiently large perfect target,
the previous extension theorem produces a copy of the entire source.
Thus the full persistent palette occurs on source embeddings inside every
copy of that target.

This theorem concerns *embeddings*. The circulation manuscript's
classification concerns *unlabelled copies*. For nonrigid sources, the
finite automorphism-group quotient is a separate step.
-/

namespace SuccessorTree.NonPrecompact

/-- The finite embedding Ramsey-degree bound for an arbitrary fixed
source BANANA structure. This is intentionally a statement about
embeddings, not automorphism orbits of embeddings. -/
def BananaMatrixStructure.embeddingRamseyDegreeLE
    {l r : ℕ} (A : BananaMatrixStructure l r) (t : ℕ) : Prop :=
  ∀ (lB rB : ℕ) (B : BananaMatrixStructure lB rB)
      (numColours : ℕ), 0 < numColours →
    ∃ (lC rC : ℕ) (C : BananaMatrixStructure lC rC),
      ∀ colouring : BananaMatrixEmbedding A C → Fin numColours,
        ∃ f : BananaMatrixEmbedding B C,
          ∃ colours : Finset (Fin numColours),
            colours.card ≤ t ∧
            ∀ e : BananaMatrixEmbedding A B,
              colouring (BananaMatrixEmbedding.comp f e) ∈ colours

/-- A fixed four-element substructure transfers the persistent colouring
to embeddings of the full source. For each `k`, no embedding Ramsey
bound strictly below `2^k` is possible. -/
theorem BananaMatrixStructure.not_embeddingRamseyDegreeLE_of_linePair
    {l r : ℕ} (A : BananaMatrixStructure l r)
    {b : F2}
    (i : BananaMatrixEmbedding (linePairSource b) A)
    (k t : ℕ) (ht : t < 2 ^ k) :
    ¬ A.embeddingRamseyDegreeLE t := by
  intro hdegree
  let q : ℕ := (2 ^ (k + 1) - 1) + 1
  let n : ℕ := (l + r) + q
  obtain ⟨lC, rC, C, hC⟩ :=
    hdegree n n (perfectBanana n) (2 ^ k) (by positivity)
  obtain ⟨lineColour, hpersistent⟩ :=
    exists_completionResiduePersistentColouring C k b
  let embeddingColour : BananaMatrixEmbedding A C → Fin (2 ^ k) :=
    fun e => lineColour
      ((BananaMatrixEmbedding.comp e i).toLinePairCopy)
  obtain ⟨f, colours, hcard, hinside⟩ := hC embeddingColour

  let j : BananaMatrixEmbedding (perfectBanana q) (perfectBanana n) := by
    dsimp [n]
    simpa only [Nat.add_comm q (l + r)] using
      (BananaMatrixStructure.standardPerfectBlockEmbedding q (l + r))

  have hall (c : Fin (2 ^ k)) : c ∈ colours := by
    obtain ⟨P, hP⟩ :=
      hpersistent (BananaMatrixEmbedding.comp f j) c
    let P' : BananaLinePairCopy (perfectBanana n) b :=
      j.mapLinePairCopy P
    obtain ⟨e, he⟩ :=
      A.exists_extend_linePairCopy i q P'
    have hcompat :
        ((BananaMatrixEmbedding.comp
            (BananaMatrixEmbedding.comp f e) i).toLinePairCopy) =
          f.mapLinePairCopy
            ((BananaMatrixEmbedding.comp e i).toLinePairCopy) := by
      apply BananaLinePairCopy.eq_of_vectors <;> rfl
    have hvalue : embeddingColour (BananaMatrixEmbedding.comp f e) = c := by
      change lineColour
        ((BananaMatrixEmbedding.comp
          (BananaMatrixEmbedding.comp f e) i).toLinePairCopy) = c
      rw [hcompat, he]
      change lineColour (f.mapLinePairCopy (j.mapLinePairCopy P)) = c
      rw [← BananaMatrixEmbedding.mapLinePairCopy_comp j f P]
      exact hP
    have hmem := hinside e
    rw [hvalue] at hmem
    exact hmem

  have huniv : colours = Finset.univ := by
    ext c
    simp only [Finset.mem_univ, iff_true]
    exact hall c
  have htooMany : 2 ^ k ≤ t := by
    rw [huniv] at hcard
    simpa using hcard
  exact (Nat.not_le_of_gt ht) htooMany

/-- Any two-sided source containing a line pair has infinite
embedding Ramsey degree. -/
theorem BananaMatrixStructure.embeddingRamseyDegree_infinite_of_linePair
    {l r : ℕ} (A : BananaMatrixStructure l r)
    {b : F2}
    (i : BananaMatrixEmbedding (linePairSource b) A) :
    ∀ t : ℕ, ¬ A.embeddingRamseyDegreeLE t := by
  intro t
  exact A.not_embeddingRamseyDegreeLE_of_linePair
    i t t t.lt_two_pow_self

/-- Every finite BANANA structure with two positive-dimensional sorts
has infinite embedding Ramsey degree. -/
theorem BananaMatrixStructure.embeddingRamseyDegree_infinite_of_positive
    {l r : ℕ} (A : BananaMatrixStructure l r)
    (hl : 0 < l) (hr : 0 < r) :
    ∀ t : ℕ, ¬ A.embeddingRamseyDegreeLE t := by
  obtain ⟨b, ⟨P⟩⟩ := A.exists_linePairCopy_of_positive hl hr
  exact A.embeddingRamseyDegree_infinite_of_linePair
    P.toSourceEmbedding

end SuccessorTree.NonPrecompact
