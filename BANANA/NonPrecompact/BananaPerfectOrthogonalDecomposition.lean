import BANANA.NonPrecompact.PerfectHomogeneity
import Mathlib.LinearAlgebra.Matrix.Dual

/-!
# Canonical orthogonal decompositions of finite perfect BANANA pairs

Given an embedding E : B_m ↪ B_n of finite standard perfect pairings,
the ambient spaces split into the image of E on each sort and an
annihilator of the embedded opposite sort.

The projection maps are obtained from perfect duality. The already
verified rightPairingMap E is a retraction of E.left; its left/right
dual counterpart retracts E.right. We record both retractions and
the resulting orthogonal decompositions, without choosing bases for
the complements.

This supplies the linear algebra needed for the arbitrary perfect-total
system amalgamation in the ample-generics proof.
-/

namespace SuccessorTree.NonPrecompact

open scoped Matrix

/-- Pairing with the embedded left sort, represented as a vector in
the source right-coordinate space by perfect finite-dimensional duality. -/
noncomputable def perfectLeftPairingMap
    {m n : ℕ}
    (E : BananaMatrixEmbedding (perfectBanana m) (perfectBanana n)) :
    (Fin n → F2) →ₗ[F2] (Fin m → F2) :=
  (dotDualEquiv m).symm.toLinearMap.comp
    (E.left.dualMap.comp (dotDualEquiv n).toLinearMap)

/-- The new left-pairing map records all pairings with the embedded
left sort, with the ambient vector on the right. -/
theorem perfectLeftPairingMap_pairing
    {m n : ℕ}
    (E : BananaMatrixEmbedding (perfectBanana m) (perfectBanana n))
    (x : Fin m → F2) (y : Fin n → F2) :
    E.left x ⬝ᵥ y = x ⬝ᵥ perfectLeftPairingMap E y := by
  have h := (dotDualEquiv m).apply_symm_apply
    (E.left.dualMap (dotDualEquiv n y))
  have hx := congrArg
    (fun φ : Module.Dual F2 (Fin m → F2) => φ x) h
  have hs :
      perfectLeftPairingMap E y ⬝ᵥ x = y ⬝ᵥ E.left x := by
    change (dotDualEquiv m (perfectLeftPairingMap E y)) x =
      (E.left.dualMap (dotDualEquiv n y)) x
    exact hx
  calc
    E.left x ⬝ᵥ y = y ⬝ᵥ E.left x := by
      rw [dotProduct_comm]
    _ = perfectLeftPairingMap E y ⬝ᵥ x := hs.symm
    _ = x ⬝ᵥ perfectLeftPairingMap E y := by
      rw [dotProduct_comm]

/-- The canonical right-pairing map is a retraction of the embedded
left sort, since the source pairing is perfect. -/
theorem rightPairingMap_left_retraction
    {m n : ℕ}
    (E : BananaMatrixEmbedding (perfectBanana m) (perfectBanana n))
    (x : Fin m → F2) :
    rightPairingMap E (E.left x) = x := by
  apply dotProduct_eq
  intro y
  calc
    rightPairingMap E (E.left x) ⬝ᵥ y =
        E.left x ⬝ᵥ E.right y :=
      (rightPairingMap_pairing E (E.left x) y).symm
    _ = x ⬝ᵥ y := by
      simpa only [perfectBanana_eval] using E.pairing_apply x y

/-- Dually, the left-pairing map is a retraction of the embedded
right sort of a finite perfect pairing. -/
theorem perfectLeftPairingMap_right_retraction
    {m n : ℕ}
    (E : BananaMatrixEmbedding (perfectBanana m) (perfectBanana n))
    (y : Fin m → F2) :
    perfectLeftPairingMap E (E.right y) = y := by
  apply dotProduct_eq
  intro x
  calc
    perfectLeftPairingMap E (E.right y) ⬝ᵥ x =
        x ⬝ᵥ perfectLeftPairingMap E (E.right y) := by
          rw [dotProduct_comm]
    _ = E.left x ⬝ᵥ E.right y :=
      (perfectLeftPairingMap_pairing E x (E.right y)).symm
    _ = x ⬝ᵥ y := by
          simpa only [perfectBanana_eval] using E.pairing_apply x y
    _ = y ⬝ᵥ x := by
          rw [dotProduct_comm]

/-- Every ambient left vector splits into an image vector and a
vector annihilating the embedded right sort. -/
theorem perfectPair_left_orthogonal_decomposition
    {m n : ℕ}
    (E : BananaMatrixEmbedding (perfectBanana m) (perfectBanana n))
    (x : Fin n → F2) :
    ∃ a : Fin m → F2, ∃ z : Fin n → F2,
      (∀ y : Fin m → F2, z ⬝ᵥ E.right y = 0) ∧
      x = E.left a + z := by
  let a := rightPairingMap E x
  let z := x - E.left a
  have hz : rightPairingMap E z = 0 := by
    simp [z, a, rightPairingMap_left_retraction]
  refine ⟨a, z, ?_, ?_⟩
  · intro y
    have hy := rightPairingMap_pairing E z y
    simpa [hz] using hy
  · dsimp [z]
    abel

/-- Every ambient right vector likewise splits into an image vector
and a vector annihilating the embedded left sort. -/
theorem perfectPair_right_orthogonal_decomposition
    {m n : ℕ}
    (E : BananaMatrixEmbedding (perfectBanana m) (perfectBanana n))
    (y : Fin n → F2) :
    ∃ b : Fin m → F2, ∃ z : Fin n → F2,
      (∀ x : Fin m → F2, E.left x ⬝ᵥ z = 0) ∧
      y = E.right b + z := by
  let b := perfectLeftPairingMap E y
  let z := y - E.right b
  have hz : perfectLeftPairingMap E z = 0 := by
    simp [z, b, perfectLeftPairingMap_right_retraction]
  refine ⟨b, z, ?_, ?_⟩
  · intro x
    have hx := perfectLeftPairingMap_pairing E x z
    simpa [hz] using hx
  · dsimp [z]
    abel

end SuccessorTree.NonPrecompact
