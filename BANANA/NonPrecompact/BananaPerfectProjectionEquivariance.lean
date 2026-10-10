import BANANA.NonPrecompact.BananaPerfectOrthogonalDecomposition
import BANANA.NonPrecompact.PerfectTotalInvariantComplements

/-!
# Equivariance of the canonical projections of embedded perfect pairs

For an automorphism of the ambient perfect pairing that intertwines
a source perfect self-automorphism, each canonical pairing retraction
is equivariant with the respective source automorphism.

The proof uses the explicit orthogonal decompositions and invariance
of the annihilators under total automorphisms. It avoids any basis
choices for the complements.
-/

namespace SuccessorTree.NonPrecompact

open scoped Matrix

/-- The left pairing retraction commutes with ambient and source
left actions in any compatible perfect-total system. -/
theorem rightPairingMap_intertwines_perfectTotal
    {m n : ℕ}
    (E : BananaMatrixEmbedding (perfectBanana m) (perfectBanana n))
    (F : BananaMatrixEmbedding (perfectBanana m) (perfectBanana m))
    (H : BananaMatrixEmbedding (perfectBanana n) (perfectBanana n))
    (hL : ∀ a, H.left (E.left a) = E.left (F.left a))
    (hR : ∀ b, H.right (E.right b) = E.right (F.right b))
    (x : Fin n → F2) :
    rightPairingMap E (H.left x) =
      F.left (rightPairingMap E x) := by
  obtain ⟨a, z, hz, hx⟩ :=
    perfectPair_left_orthogonal_decomposition E x
  have hzq : rightPairingMap E z = 0 := by
    apply dotProduct_eq
    intro b
    calc
      rightPairingMap E z ⬝ᵥ b = z ⬝ᵥ E.right b :=
        (rightPairingMap_pairing E z b).symm
      _ = 0 := hz b
      _ = (0 : Fin m → F2) ⬝ᵥ b := by simp
  have hHz : ∀ b : Fin m → F2,
      H.left z ⬝ᵥ E.right b = 0 :=
    perfectPair_leftAnnihilator_invariant_of_total E F H hR z hz
  have hHzq : rightPairingMap E (H.left z) = 0 := by
    apply dotProduct_eq
    intro b
    calc
      rightPairingMap E (H.left z) ⬝ᵥ b =
          H.left z ⬝ᵥ E.right b :=
        (rightPairingMap_pairing E (H.left z) b).symm
      _ = 0 := hHz b
      _ = (0 : Fin m → F2) ⬝ᵥ b := by simp
  have hxq : rightPairingMap E x = a := by
    rw [hx, map_add, rightPairingMap_left_retraction, hzq, add_zero]
  calc
    rightPairingMap E (H.left x) =
        rightPairingMap E (H.left (E.left a + z)) := by rw [hx]
    _ = rightPairingMap E (E.left (F.left a) + H.left z) := by
          rw [map_add, hL a]
    _ = F.left a := by
          rw [map_add, rightPairingMap_left_retraction, hHzq]
          simp
    _ = F.left (rightPairingMap E x) := by rw [hxq]

/-- The right pairing retraction likewise intertwines the ambient
and source right actions. -/
theorem perfectLeftPairingMap_intertwines_perfectTotal
    {m n : ℕ}
    (E : BananaMatrixEmbedding (perfectBanana m) (perfectBanana n))
    (F : BananaMatrixEmbedding (perfectBanana m) (perfectBanana m))
    (H : BananaMatrixEmbedding (perfectBanana n) (perfectBanana n))
    (hL : ∀ a, H.left (E.left a) = E.left (F.left a))
    (hR : ∀ b, H.right (E.right b) = E.right (F.right b))
    (y : Fin n → F2) :
    perfectLeftPairingMap E (H.right y) =
      F.right (perfectLeftPairingMap E y) := by
  obtain ⟨b, z, hz, hy⟩ :=
    perfectPair_right_orthogonal_decomposition E y
  have hzq : perfectLeftPairingMap E z = 0 := by
    apply dotProduct_eq
    intro a
    calc
      perfectLeftPairingMap E z ⬝ᵥ a =
          a ⬝ᵥ perfectLeftPairingMap E z := by rw [dotProduct_comm]
      _ = E.left a ⬝ᵥ z :=
        (perfectLeftPairingMap_pairing E a z).symm
      _ = 0 := hz a
      _ = (0 : Fin m → F2) ⬝ᵥ a := by simp
  have hHz : ∀ a : Fin m → F2,
      E.left a ⬝ᵥ H.right z = 0 :=
    perfectPair_rightAnnihilator_invariant_of_total E F H hL z hz
  have hHzq : perfectLeftPairingMap E (H.right z) = 0 := by
    apply dotProduct_eq
    intro a
    calc
      perfectLeftPairingMap E (H.right z) ⬝ᵥ a =
          a ⬝ᵥ perfectLeftPairingMap E (H.right z) := by rw [dotProduct_comm]
      _ = E.left a ⬝ᵥ H.right z :=
        (perfectLeftPairingMap_pairing E a (H.right z)).symm
      _ = 0 := hHz a
      _ = (0 : Fin m → F2) ⬝ᵥ a := by simp
  have hyq : perfectLeftPairingMap E y = b := by
    rw [hy, map_add, perfectLeftPairingMap_right_retraction, hzq, add_zero]
  calc
    perfectLeftPairingMap E (H.right y) =
        perfectLeftPairingMap E (H.right (E.right b + z)) := by rw [hy]
    _ = perfectLeftPairingMap E (E.right (F.right b) + H.right z) := by
          rw [map_add, hR b]
    _ = F.right b := by
          rw [map_add, perfectLeftPairingMap_right_retraction, hHzq]
          simp
    _ = F.right (perfectLeftPairingMap E y) := by rw [hyq]

end SuccessorTree.NonPrecompact
