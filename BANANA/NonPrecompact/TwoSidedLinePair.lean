import BANANA.NonPrecompact.CopyRamseyDegree
import Mathlib.LinearAlgebra.StdBasis

/-!
# Four-element line-pair substructures of two-sided BANANA structures

A BANANA structure whose two vector-space sorts are both nonzero contains
a four-element line-pair substructure, of pairing value determined by a
chosen pair of nonzero vectors. This formalises the structural reduction
used in the nonzero/nonzero half of the manuscript's copy Ramsey-degree
classification.

A line-pair copy is a pair of nonzero vectors of the corresponding
pairing value, as in `CopyRamseyDegree.lean`. The lemmas below do not
assert the remaining degree-propagation theorem for arbitrary source
structures.
-/

namespace SuccessorTree.NonPrecompact

/-- A standard coordinate vector with one nonzero entry, whenever the
coordinate space has positive dimension. -/
private def coordinateUnit (n : ℕ) (hn : 0 < n) : Fin n → F2 :=
  Pi.single ⟨0, hn⟩ 1

private theorem coordinateUnit_ne_zero (n : ℕ) (hn : 0 < n) :
    coordinateUnit n hn ≠ 0 := by
  intro heq
  have hcoord := congrFun heq (⟨0, hn⟩ : Fin n)
  have hfalse : (1 : F2) = 0 := by
    simpa [coordinateUnit] using hcoord
  exact one_ne_zero hfalse

/-- Every chosen pair of nonzero vectors determines a rigid four-element
BANANA line-pair copy. Its pairing value is automatically the right one. -/
def BananaMatrixStructure.linePairCopyOfNonzero
    {l r : ℕ} (A : BananaMatrixStructure l r)
    (x : Fin l → F2) (y : Fin r → F2)
    (hx : x ≠ 0) (hy : y ≠ 0) :
    BananaLinePairCopy A (A.eval x y) where
  left := x
  right := y
  left_ne_zero := hx
  right_ne_zero := hy
  pairing := rfl

/-- A structure with both sorts positive-dimensional contains a
four-element line-pair copy for some pairing value `b ∈ F₂`. -/
theorem BananaMatrixStructure.exists_linePairCopy_of_positive
    {l r : ℕ} (A : BananaMatrixStructure l r)
    (hl : 0 < l) (hr : 0 < r) :
    ∃ b : F2, Nonempty (BananaLinePairCopy A b) := by
  let x := coordinateUnit l hl
  let y := coordinateUnit r hr
  exact ⟨A.eval x y, ⟨A.linePairCopyOfNonzero x y
    (coordinateUnit_ne_zero l hl)
    (coordinateUnit_ne_zero r hr)⟩⟩

/-- A line-pair copy of a fixed pairing value maps compatibly through
two successive BANANA embeddings. -/
theorem BananaMatrixEmbedding.mapLinePairCopy_comp
    {l₁ r₁ l₂ r₂ l₃ r₃ : ℕ}
    {A : BananaMatrixStructure l₁ r₁}
    {B : BananaMatrixStructure l₂ r₂}
    {C : BananaMatrixStructure l₃ r₃}
    (f : BananaMatrixEmbedding A B)
    (g : BananaMatrixEmbedding B C)
    {b : F2} (P : BananaLinePairCopy A b) :
    (BananaMatrixEmbedding.comp g f).mapLinePairCopy P =
      g.mapLinePairCopy (f.mapLinePairCopy P) := by
  cases P
  rfl

end SuccessorTree.NonPrecompact
