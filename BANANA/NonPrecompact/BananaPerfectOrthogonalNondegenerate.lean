import BANANA.NonPrecompact.BananaPerfectOrthogonalDecomposition

/-!
# Nondegeneracy of the orthogonal complement of a perfect BANANA subpair

Let E : B_m ↪ B_n be an embedding of finite perfect pairings.
An ambient left vector that annihilates both the embedded right
sort and every right-annihilator of the embedded left sort must
vanish. Dually, an ambient right vector that annihilates both
the embedded left sort and its left-annihilator must vanish.

Together with the two canonical orthogonal decompositions, these
statements prove that the pairing induced between the orthogonal
complements is perfect (nondegenerate on both sides), without
choosing bases or defining an explicit complement matrix.
-/

namespace SuccessorTree.NonPrecompact

open scoped Matrix

/-- Nondegeneracy on the left of the induced orthogonal-complement
pairing, expressed using annihilator conditions on both sorts. -/
theorem perfectPair_leftComplement_nondegenerate
    {m n : ℕ}
    (E : BananaMatrixEmbedding (perfectBanana m) (perfectBanana n))
    (x : Fin n → F2)
    (hxA : ∀ y : Fin m → F2, x ⬝ᵥ E.right y = 0)
    (hxK : ∀ z : Fin n → F2,
      (∀ a : Fin m → F2, E.left a ⬝ᵥ z = 0) →
      x ⬝ᵥ z = 0) :
    x = 0 := by
  apply dotProduct_eq
  intro v
  obtain ⟨a, z, hz, hv⟩ :=
    perfectPair_right_orthogonal_decomposition E v
  calc
    x ⬝ᵥ v = x ⬝ᵥ (E.right a + z) := by rw [hv]
    _ = x ⬝ᵥ E.right a + x ⬝ᵥ z := by rw [dotProduct_add]
    _ = 0 := by rw [hxA a, hxK z hz, zero_add]
    _ = (0 : Fin n → F2) ⬝ᵥ v := by simp

/-- Nondegeneracy on the right of the induced pairing between
the two annihilators of an embedded finite perfect subpair. -/
theorem perfectPair_rightComplement_nondegenerate
    {m n : ℕ}
    (E : BananaMatrixEmbedding (perfectBanana m) (perfectBanana n))
    (y : Fin n → F2)
    (hyA : ∀ x : Fin m → F2, E.left x ⬝ᵥ y = 0)
    (hyK : ∀ z : Fin n → F2,
      (∀ a : Fin m → F2, z ⬝ᵥ E.right a = 0) →
      z ⬝ᵥ y = 0) :
    y = 0 := by
  apply dotProduct_eq
  intro v
  obtain ⟨a, z, hz, hv⟩ :=
    perfectPair_left_orthogonal_decomposition E v
  calc
    y ⬝ᵥ v = v ⬝ᵥ y := by rw [dotProduct_comm]
    _ = (E.left a + z) ⬝ᵥ y := by rw [hv]
    _ = E.left a ⬝ᵥ y + z ⬝ᵥ y := by rw [add_dotProduct]
    _ = 0 := by rw [hyA a, hyK z hz, zero_add]
    _ = (0 : Fin n → F2) ⬝ᵥ v := by simp

end SuccessorTree.NonPrecompact
