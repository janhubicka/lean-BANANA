import BANANA.NonPrecompact.PairingCopies
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Completing one side of a perfect BANANA copy

The degree-one half of the BANANA copy-Ramsey classification uses the
following elementary linear-algebra fact.  If a D-dimensional subspace W of
an ambient perfect pairing is chosen on the left, then W can be completed to
a copy of the standard perfect pairing B_D by choosing dual coordinate
functionals on the right.

In coordinates this amounts to the following statement: every injective
linear map L : F₂^d → F₂^n admits an injective right map R such that

  L x · R y = x · y.

Choose a linear left inverse Q of L and take R to be the transpose of Q.
-/

namespace SuccessorTree.NonPrecompact

open scoped Matrix

/-- The transpose of a linear left inverse provides the right-hand map of a
perfect-pair embedding. -/
noncomputable def rightMapOfLeftInverse
    {d n : ℕ}
    (Q : (Fin n → F2) →ₗ[F2] (Fin d → F2)) :
    (Fin d → F2) →ₗ[F2] (Fin n → F2) :=
  (LinearMap.toMatrix' Q)ᵀ.mulVecLin

@[simp] theorem rightMapOfLeftInverse_apply
    {d n : ℕ}
    (Q : (Fin n → F2) →ₗ[F2] (Fin d → F2))
    (y : Fin d → F2) :
    rightMapOfLeftInverse Q y =
      (LinearMap.toMatrix' Q)ᵀ *ᵥ y := rfl

/-- If Q is a left inverse of L, then the transpose of Q is adjoint to L
with respect to the standard dot products. -/
theorem pairing_rightMapOfLeftInverse
    {d n : ℕ}
    (L : (Fin d → F2) →ₗ[F2] (Fin n → F2))
    (Q : (Fin n → F2) →ₗ[F2] (Fin d → F2))
    (hQ : Q.comp L = LinearMap.id)
    (x y : Fin d → F2) :
    L x ⬝ᵥ rightMapOfLeftInverse Q y = x ⬝ᵥ y := by
  change
    L x ⬝ᵥ (LinearMap.toMatrix' Q)ᵀ *ᵥ y = x ⬝ᵥ y
  rw [Matrix.dotProduct_transpose_mulVec]
  rw [LinearMap.toMatrix'_mulVec]
  have hQL : Q (L x) = x := by
    have h := LinearMap.congr_fun hQ x
    simpa using h
  rw [hQL, dotProduct_comm]

/-- The transpose-of-left-inverse right map is injective. -/
theorem rightMapOfLeftInverse_injective
    {d n : ℕ}
    (L : (Fin d → F2) →ₗ[F2] (Fin n → F2))
    (Q : (Fin n → F2) →ₗ[F2] (Fin d → F2))
    (hQ : Q.comp L = LinearMap.id) :
    Function.Injective (rightMapOfLeftInverse Q) := by
  intro y₁ y₂ h
  apply dotProduct_eq
  intro x
  calc
    y₁ ⬝ᵥ x = x ⬝ᵥ y₁ := dotProduct_comm _ _
    _ = L x ⬝ᵥ rightMapOfLeftInverse Q y₁ :=
      (pairing_rightMapOfLeftInverse L Q hQ x y₁).symm
    _ = L x ⬝ᵥ rightMapOfLeftInverse Q y₂ := by rw [h]
    _ = x ⬝ᵥ y₂ :=
      pairing_rightMapOfLeftInverse L Q hQ x y₂
    _ = y₂ ⬝ᵥ x := dotProduct_comm _ _

/-- Every injective left linear map into a standard perfect pairing extends
to an embedding of standard perfect pairings.

This formalises the manuscript sentence "extend the dual coordinate
functionals of a basis of W to V". -/
theorem exists_perfectPairEmbedding_with_left
    {d n : ℕ}
    (L : (Fin d → F2) →ₗ[F2] (Fin n → F2))
    (hL : Function.Injective L) :
    ∃ E : PerfectPairEmbedding d n, E.left = L := by
  have hker : LinearMap.ker L = ⊥ :=
    LinearMap.ker_eq_bot.mpr hL
  obtain ⟨Q, hQ⟩ :=
    L.exists_leftInverse_of_injective hker
  let R : (Fin d → F2) →ₗ[F2] (Fin n → F2) :=
    rightMapOfLeftInverse Q
  let E : PerfectPairEmbedding d n := {
    left := L
    right := R
    left_injective := hL
    right_injective := by
      simpa [R] using rightMapOfLeftInverse_injective L Q hQ
    pairing_apply := by
      intro x y
      simpa [R] using pairing_rightMapOfLeftInverse L Q hQ x y
  }
  exact ⟨E, rfl⟩

end SuccessorTree.NonPrecompact
