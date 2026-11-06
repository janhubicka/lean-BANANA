import BANANA.NonPrecompact.SymplecticAlternatingAdaptedCoordinates
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# Alternating forms and their chosen-coordinate F₂ matrices

The geometric class is defined by *alternation on every vector*.
The zero-cross matrix construction uses symmetric matrices with
zero diagonal. This module explicitly checks the implication from
an original alternating bilinear form to the matrix hypotheses.

The source form may be degenerate, the carrier may be zero, and the
coordinate index may be empty. No perfectness assumption is used.

DRAFT / NOT KERNEL-VERIFIED. This is not an author-approved repair
of the circulation TeX.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical

/-- Any alternating F₂-bilinear form has a zero-diagonal matrix
relative to arbitrary standard function-space coordinates. -/
theorem symplecticAlternating_toMatrix_diag_zero
    {I : Type*} [Fintype I]
    (β : LinearMap.BilinForm F2 (I → F2))
    (hβ : β.IsAlt) :
    ∀ i : I, (LinearMap.BilinForm.toMatrix' β) i i = 0 := by
  intro i
  rw [LinearMap.BilinForm.toMatrix'_apply]
  exact hβ (Pi.single i 1)

/-- Over F₂, alternation implies symmetry. Thus no independent
symmetry hypothesis is needed for an alternating form's matrix. -/
theorem symplecticAlternating_toMatrix_symmetric
    {I : Type*} [Fintype I]
    (β : LinearMap.BilinForm F2 (I → F2))
    (hβ : β.IsAlt) :
    ∀ i j : I,
      (LinearMap.BilinForm.toMatrix' β) i j =
      (LinearMap.BilinForm.toMatrix' β) j i := by
  intro i j
  simp only [LinearMap.BilinForm.toMatrix'_apply]
  have hneg := hβ.neg_eq (Pi.single i 1) (Pi.single j 1)
  rcases f2_eq_zero_or_one (β (Pi.single i 1) (Pi.single j 1)) with hz | ho
  · simpa [hz] using hneg
  · simpa [ho] using hneg

/-- Both exact matrix assumptions used for the strong amalgam
follow from alternation, even for degenerate forms. -/
theorem symplecticAlternating_toMatrix_certificate
    {I : Type*} [Fintype I]
    (β : LinearMap.BilinForm F2 (I → F2))
    (hβ : β.IsAlt) :
    (∀ i, (LinearMap.BilinForm.toMatrix' β) i i = 0) ∧
    (∀ i j, (LinearMap.BilinForm.toMatrix' β) i j =
      (LinearMap.BilinForm.toMatrix' β) j i) := by
  exact ⟨symplecticAlternating_toMatrix_diag_zero β hβ,
    symplecticAlternating_toMatrix_symmetric β hβ⟩

end SuccessorTree.NonPrecompact
