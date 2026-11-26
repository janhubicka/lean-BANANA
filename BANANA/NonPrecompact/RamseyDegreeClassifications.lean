import BANANA.NonPrecompact.NativeEmbeddingCopyDegree
import BANANA.NonPrecompact.SymplecticCopyDegree

/-!
# Embedding Ramsey degrees for finite alternating spaces
-/

namespace SuccessorTree.NonPrecompact

open Module

namespace FiniteAlternatingSpace

/-- The embedding-degree classification agrees with the copy-degree
classification: the zero space has degree one and all other spaces
have infinite degree. -/
theorem embeddingRamseyDegree_classification (A : FiniteAlternatingSpace) (t : ℕ) :
    copySystem.EmbeddingRamseyDegreeLE A t ↔ finrank F2 A.carrier = 0 ∧ 1 ≤ t := by
  let H := uniformEmbeddingFibres A
  rw [H.embeddingRamseyDegreeLE_iff_copyRamseyDegreeLE_div, copyRamseyDegree_classification]
  constructor
  · rintro ⟨hA, ht⟩
    have m_le : Nat.card (copySystem.ReductAutomorphism A) ≤ t :=
      by simpa using (Nat.le_div_iff_mul_le H.size_pos).mp ht
    exact ⟨hA, H.size_pos.trans_le m_le⟩
  · rintro ⟨hA, ht⟩
    exact ⟨hA, by simpa [card_reductAutomorphism_of_finrank_zero A hA] using ht⟩

end FiniteAlternatingSpace

end SuccessorTree.NonPrecompact
