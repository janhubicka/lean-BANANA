import BANANA.NonPrecompact.BananaStrongBlockAmalgam
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Retractions and pullbacks for arbitrary BANANA amalgamation diagrams

The full strong amalgamation property does not require that the common
source be the first coordinate block in each target. A finite-dimensional
injective linear map admits a linear retraction. These retractions
allow explicit constructions in redundant ambient coordinates.

We also record a matrix version of pulling back a finite bilinear
pairing along arbitrary linear maps. This is the algebraic interface
needed to construct a strong amalgam without choosing bases for
complementary subspaces in the two targets.
-/

namespace SuccessorTree.NonPrecompact

open scoped Matrix

/-- Any BANANA embedding admits linear retractions, independently on
its left and right vector-space sorts. Retractions need not preserve
the bilinear pairing: only their compositions with the embedding
are required to be the identity. -/
theorem BananaMatrixEmbedding.exists_sort_retractions
    {aL aR bL bR : ℕ}
    {A : BananaMatrixStructure aL aR}
    {B : BananaMatrixStructure bL bR}
    (f : BananaMatrixEmbedding A B) :
    ∃ pL : (Fin bL → F2) →ₗ[F2] (Fin aL → F2),
    ∃ pR : (Fin bR → F2) →ₗ[F2] (Fin aR → F2),
      (∀ x, pL (f.left x) = x) ∧
      (∀ y, pR (f.right y) = y) := by
  obtain ⟨pL, hpL⟩ :=
    f.left.exists_leftInverse_of_injective
      (LinearMap.ker_eq_bot.mpr f.left_injective)
  obtain ⟨pR, hpR⟩ :=
    f.right.exists_leftInverse_of_injective
      (LinearMap.ker_eq_bot.mpr f.right_injective)
  refine ⟨pL, pR, ?_, ?_⟩
  · intro x
    have h := LinearMap.congr_fun hpL x
    simpa only [LinearMap.comp_apply, LinearMap.id_apply] using h
  · intro y
    have h := LinearMap.congr_fun hpR y
    simpa only [LinearMap.comp_apply, LinearMap.id_apply] using h

/-- Matrix of a bilinear form pulled back along a left linear map
and a right linear map (with no injectivity assumptions). -/
def bananaPairingPullback
    {aL aR bL bR : ℕ}
    (B : BananaMatrixStructure bL bR)
    (fL : (Fin aL → F2) →ₗ[F2] (Fin bL → F2))
    (fR : (Fin aR → F2) →ₗ[F2] (Fin bR → F2)) :
    BananaMatrixStructure aL aR where
  pairing := (LinearMap.toMatrix' fL)ᵀ *
    B.pairing * (LinearMap.toMatrix' fR)

/-- Evaluating the pulled-back matrix agrees with evaluating the
original pairing on the images of the two linear maps. -/
theorem bananaPairingPullback_eval
    {aL aR bL bR : ℕ}
    (B : BananaMatrixStructure bL bR)
    (fL : (Fin aL → F2) →ₗ[F2] (Fin bL → F2))
    (fR : (Fin aR → F2) →ₗ[F2] (Fin bR → F2))
    (x : Fin aL → F2) (y : Fin aR → F2) :
    (bananaPairingPullback B fL fR).eval x y =
      B.eval (fL x) (fR y) := by
  change x ⬝ᵥ
      (((LinearMap.toMatrix' fL)ᵀ *
        B.pairing * (LinearMap.toMatrix' fR)) *ᵥ y) =
    (fL x) ⬝ᵥ (B.pairing *ᵥ (fR y))
  rw [Matrix.mulVec_mulVec]
  rw [LinearMap.toMatrix'_mulVec]
  rw [Matrix.mulVec_mulVec]
  rw [Matrix.dotProduct_transpose_mulVec]
  rw [LinearMap.toMatrix'_mulVec]
  exact dotProduct_comm _ _

/-- Pointwise sum of two pairings on the same finite coordinate spaces. -/
def bananaPairingAdd
    {l r : ℕ} (A B : BananaMatrixStructure l r) :
    BananaMatrixStructure l r where
  pairing := A.pairing + B.pairing

/-- The evaluation of a pointwise sum of pairing matrices splits
as the sum of the two bilinear evaluations. -/
theorem bananaPairingAdd_eval
    {l r : ℕ} (A B : BananaMatrixStructure l r)
    (x : Fin l → F2) (y : Fin r → F2) :
    (bananaPairingAdd A B).eval x y =
      A.eval x y + B.eval x y := by
  simp [bananaPairingAdd, BananaMatrixStructure.eval,
    Matrix.add_mulVec, dotProduct_add]

end SuccessorTree.NonPrecompact
