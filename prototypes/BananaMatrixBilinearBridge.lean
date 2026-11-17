import BANANA.NonPrecompact.BananaArbitraryAmalgamTools
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.BilinearMap

/-!
# Prototype: finite rectangular BANANA pairings as bundled bilinear maps

**Experimental and not yet kernel-checked.** This source is deliberately
outside the production `BANANA` graph. It uses matrix and bilinear APIs
verified to be present at the pinned mathlib revision.

Unlike `BilinForm`, the curried `LinearMap` representation allows
different left/right dimensions. We retain existing matrix definitions
and derive bundled equations from their previously proved evaluations.
-/

namespace SuccessorTree.NonPrecompact

open scoped Matrix

/-- A rectangular finite pairing bundled as a mathlib bilinear map
between the genuinely distinct left and right vector-space sorts.

The matrix-vector operation and the dot product are already bundled in
mathlib, so no new bilinearity calculations are required. -/
noncomputable def BananaMatrixStructure.toBilinearMap
    {l r : ℕ} (A : BananaMatrixStructure l r) :
    (Fin l → F2) →ₗ[F2] (Fin r → F2) →ₗ[F2] F2 :=
  (Matrix.dotProductBilin (m := Fin l) F2 F2).compl₂ A.pairing.mulVecLin

@[simp] theorem BananaMatrixStructure.toBilinearMap_apply
    {l r : ℕ} (A : BananaMatrixStructure l r)
    (x : Fin l → F2) (y : Fin r → F2) :
    A.toBilinearMap x y = A.eval x y := rfl

/-- The matrix pullback from the existing finite-amalgamation module
coincides with the standard bilinear pullback. -/
theorem bananaPairingPullback_toBilinearMap
    {aL aR bL bR : ℕ}
    (B : BananaMatrixStructure bL bR)
    (fL : (Fin aL → F2) →ₗ[F2] (Fin bL → F2))
    (fR : (Fin aR → F2) →ₗ[F2] (Fin bR → F2)) :
    (bananaPairingPullback B fL fR).toBilinearMap =
      B.toBilinearMap.compl₁₂ fL fR := by
  apply LinearMap.ext₂
  intro x y
  change (bananaPairingPullback B fL fR).eval x y =
    B.eval (fL x) (fR y)
  exact bananaPairingPullback_eval B fL fR x y

/-- Pairing preservation by a finite BANANA embedding is an equality
of bundled bilinear maps, which composes by the standard library API. -/
theorem BananaMatrixEmbedding.isometry_bilinearMap
    {l r l' r' : ℕ}
    {A : BananaMatrixStructure l r}
    {B : BananaMatrixStructure l' r'}
    (e : BananaMatrixEmbedding A B) :
    B.toBilinearMap.compl₁₂ e.left e.right = A.toBilinearMap := by
  apply LinearMap.ext₂
  intro x y
  change B.eval (e.left x) (e.right y) = A.eval x y
  exact e.pairing_apply x y

end SuccessorTree.NonPrecompact

#print axioms SuccessorTree.NonPrecompact.BananaMatrixStructure.toBilinearMap
#print axioms SuccessorTree.NonPrecompact.bananaPairingPullback_toBilinearMap
#print axioms SuccessorTree.NonPrecompact.BananaMatrixEmbedding.isometry_bilinearMap
