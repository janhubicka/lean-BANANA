import BANANA.NonPrecompact.BananaPerfectOrthogonalDecomposition

/-!
# The pairing splits over the orthogonal complement

Let E : B_m ↪ B_n be an embedded finite perfect pair.
The pairing between two ambient vectors decomposed into their
images from B_m and their respective annihilator components is
the source perfect pairing plus the induced pairing between
the two annihilators.

The mixed terms vanish. This is the pairing-preserving
direct-sum calculation needed to transport arbitrary
perfect-total systems to split coordinates.
-/

namespace SuccessorTree.NonPrecompact

open scoped Matrix

/-- The embedded left sort is orthogonal to the kernel of the
canonical right pairing projection. -/
theorem perfectPair_mixed_pairing_left_zero
    {m n : ℕ}
    (E : BananaMatrixEmbedding (perfectBanana m) (perfectBanana n))
    (a : Fin m → F2)
    (z : LinearMap.ker (perfectLeftPairingMap E)) :
    E.left a ⬝ᵥ (z : Fin n → F2) = 0 := by
  have hz : perfectLeftPairingMap E (z : Fin n → F2) = 0 :=
    (LinearMap.mem_ker).mp z.property
  have hp := perfectLeftPairingMap_pairing E a (z : Fin n → F2)
  simpa [hz] using hp

/-- The kernel of the canonical left pairing projection
is orthogonal to the embedded right sort. -/
theorem perfectPair_mixed_pairing_right_zero
    {m n : ℕ}
    (E : BananaMatrixEmbedding (perfectBanana m) (perfectBanana n))
    (z : LinearMap.ker (rightPairingMap E))
    (b : Fin m → F2) :
    (z : Fin n → F2) ⬝ᵥ E.right b = 0 := by
  have hz : rightPairingMap E (z : Fin n → F2) = 0 :=
    (LinearMap.mem_ker).mp z.property
  have hp := rightPairingMap_pairing E (z : Fin n → F2) b
  simpa [hz] using hp

/-- The full perfect pairing of two orthogonally decomposed
ambient vectors has no mixed terms. -/
theorem perfectPair_orthogonal_sum_pairing
    {m n : ℕ}
    (E : BananaMatrixEmbedding (perfectBanana m) (perfectBanana n))
    (a b : Fin m → F2)
    (zL : LinearMap.ker (rightPairingMap E))
    (zR : LinearMap.ker (perfectLeftPairingMap E)) :
    (E.left a + (zL : Fin n → F2)) ⬝ᵥ
        (E.right b + (zR : Fin n → F2)) =
      a ⬝ᵥ b + (zL : Fin n → F2) ⬝ᵥ (zR : Fin n → F2) := by
  have hsource : E.left a ⬝ᵥ E.right b = a ⬝ᵥ b := by
    simpa only [perfectBanana_eval] using E.pairing_apply a b
  have hLR := perfectPair_mixed_pairing_left_zero E a zR
  have hRL := perfectPair_mixed_pairing_right_zero E zL b
  calc
    (E.left a + (zL : Fin n → F2)) ⬝ᵥ
        (E.right b + (zR : Fin n → F2)) =
      E.left a ⬝ᵥ E.right b +
      E.left a ⬝ᵥ (zR : Fin n → F2) +
      (zL : Fin n → F2) ⬝ᵥ E.right b +
      (zL : Fin n → F2) ⬝ᵥ (zR : Fin n → F2) := by
        rw [add_dotProduct, dotProduct_add, dotProduct_add]
        abel
    _ = a ⬝ᵥ b + (zL : Fin n → F2) ⬝ᵥ
        (zR : Fin n → F2) := by
          rw [hsource, hLR, hRL]
          simp

end SuccessorTree.NonPrecompact
