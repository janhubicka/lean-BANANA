import BANANA.NonPrecompact.BananaArbitraryAmalgamTools
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.BilinearMap

/-!
# Finite rectangular BANANA pairings as bundled bilinear maps

The standard two-sorted matrix pairing is represented faithfully as a
mathlib bilinear map, for arbitrary left and right dimensions. Pullback and
isometry equations then follow from the standard bilinear composition API.

In particular, successive matrix pullbacks are equal to pullback along
the composites, even for degenerate pairings or zero-dimensional sorts.
This module contains no new axioms and makes no changes to the manuscript.
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
  (dotProductBilin (m := Fin l) F2 F2).compl₂ A.pairing.mulVecLin

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

/-- The ordinary matrix-pullback operation is functorial after
bundling, by mathlib's standard composition law. This gives an
independent downstream use beyond the definition of the interface. -/
theorem bananaPairingPullback_twice_toBilinearMap
    {aL aR bL bR cL cR : ℕ}
    (C : BananaMatrixStructure cL cR)
    (fL : (Fin bL → F2) →ₗ[F2] (Fin cL → F2))
    (fR : (Fin bR → F2) →ₗ[F2] (Fin cR → F2))
    (gL : (Fin aL → F2) →ₗ[F2] (Fin bL → F2))
    (gR : (Fin aR → F2) →ₗ[F2] (Fin bR → F2)) :
    (bananaPairingPullback (bananaPairingPullback C fL fR) gL gR).toBilinearMap =
      C.toBilinearMap.compl₁₂ (fL.comp gL) (fR.comp gR) := by
  rw [bananaPairingPullback_toBilinearMap,
      bananaPairingPullback_toBilinearMap,
      LinearMap.compl₁₂_comp_comp]

/-- The bundled isometry property of two successive finite embeddings
follows immediately from the same composition law. -/
theorem BananaMatrixEmbedding.comp_isometry_bilinearMap
    {aL aR bL bR cL cR : ℕ}
    {A : BananaMatrixStructure aL aR}
    {B : BananaMatrixStructure bL bR}
    {C : BananaMatrixStructure cL cR}
    (f : BananaMatrixEmbedding A B)
    (g : BananaMatrixEmbedding B C) :
    C.toBilinearMap.compl₁₂ (g.comp f).left (g.comp f).right =
      A.toBilinearMap := by
  change C.toBilinearMap.compl₁₂ (g.left.comp f.left)
    (g.right.comp f.right) = A.toBilinearMap
  rw [LinearMap.compl₁₂_comp_comp,
      g.isometry_bilinearMap, f.isometry_bilinearMap]

/-- A rectangular matrix pairing is uniquely determined by its bundled
bilinear map. Both sorts may be zero-dimensional or have different
dimensions; no nondegeneracy hypothesis is needed. -/
theorem BananaMatrixStructure.toBilinearMap_injective
    {l r : ℕ} :
    Function.Injective
      (fun A : BananaMatrixStructure l r => A.toBilinearMap) := by
  intro A B h
  have hmatrix : A.pairing = B.pairing := by
    ext i j
    have hij := congrArg
      (fun F : (Fin l → F2) →ₗ[F2] (Fin r → F2) →ₗ[F2] F2 =>
        F (Pi.single i 1) (Pi.single j 1)) h
    simpa only [BananaMatrixStructure.toBilinearMap_apply,
      BananaMatrixStructure.eval, Matrix.mulVec_single_one,
      single_one_dotProduct, Matrix.col_apply] using hij
  cases A with
  | mk MA =>
    cases B with
    | mk MB =>
      cases hmatrix
      rfl

/-- Composition of finite rectangular pairing pullbacks holds as an
exact equality of matrix structures, not merely on evaluations.

This avoids expanding the two nested matrix products and works for
arbitrary linear maps, including degenerate and zero-dimensional sorts. -/
theorem bananaPairingPullback_comp
    {aL aR bL bR cL cR : ℕ}
    (C : BananaMatrixStructure cL cR)
    (fL : (Fin bL → F2) →ₗ[F2] (Fin cL → F2))
    (fR : (Fin bR → F2) →ₗ[F2] (Fin cR → F2))
    (gL : (Fin aL → F2) →ₗ[F2] (Fin bL → F2))
    (gR : (Fin aR → F2) →ₗ[F2] (Fin bR → F2)) :
    bananaPairingPullback (bananaPairingPullback C fL fR) gL gR =
      bananaPairingPullback C (fL.comp gL) (fR.comp gR) := by
  apply BananaMatrixStructure.toBilinearMap_injective
  change
    (bananaPairingPullback (bananaPairingPullback C fL fR) gL gR).toBilinearMap =
      (bananaPairingPullback C (fL.comp gL) (fR.comp gR)).toBilinearMap
  rw [bananaPairingPullback_twice_toBilinearMap,
    bananaPairingPullback_toBilinearMap]

end SuccessorTree.NonPrecompact
