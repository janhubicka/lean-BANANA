import BANANA.NonPrecompact.TwoSidedLinePair
import Mathlib.LinearAlgebra.StdBasis

/-!
# The four-element BANANA source as an actual substructure

For `b : F₂`, the source `linePairSource b` has one-dimensional left
and right vector-space sorts, with their basis vectors paired to `b`.
A line-pair copy in an arbitrary BANANA structure yields a genuine
pair of injective linear maps from this source, preserving the pairing.

This bridges the convenient nonzero-vector presentation of
`BananaLinePairCopy` with the ordinary structural embedding required
by the degree-propagation lemma.
-/

namespace SuccessorTree.NonPrecompact

open scoped Matrix

/-- The four-element line-pair structure with pairing value `b`. -/
def linePairSource (b : F2) : BananaMatrixStructure 1 1 where
  pairing := fun _ _ => b

/-- Every vector in a one-dimensional coordinate space is determined by
its only coordinate. -/
theorem oneCoordinate_ext
    {u v : Fin 1 → F2} (h : u 0 = v 0) : u = v := by
  funext i
  have hi : i = (0 : Fin 1) := Subsingleton.elim i 0
  simpa [hi] using h

/-- The canonical linear map sending the basis vector of `F₂¹` to `x`. -/
def linePairSpanMap {l : ℕ} (x : Fin l → F2) :
    (Fin 1 → F2) →ₗ[F2] (Fin l → F2) :=
  (LinearMap.proj (0 : Fin 1)).smulRight x

@[simp] theorem linePairSpanMap_apply
    {l : ℕ} (x : Fin l → F2) (u : Fin 1 → F2) :
    linePairSpanMap x u = u 0 • x := rfl

/-- A nonzero basis image makes the one-dimensional linear map injective. -/
theorem linePairSpanMap_injective
    {l : ℕ} {x : Fin l → F2} (hx : x ≠ 0) :
    Function.Injective (linePairSpanMap x) := by
  intro u v h
  apply oneCoordinate_ext
  apply smul_left_injective F2 hx
  simpa only [linePairSpanMap_apply] using h

@[simp] theorem linePairSource_eval
    (b : F2) (u v : Fin 1 → F2) :
    (linePairSource b).eval u v = (u 0) * (v 0) * b := by
  classical
  simp [linePairSource, BananaMatrixStructure.eval,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    mul_assoc, mul_comm, mul_left_comm]

/-- Scaling both arguments scales the value of the bilinear pairing by
the product of the two scalars. -/
theorem BananaMatrixStructure.eval_smul_smul
    {l r : ℕ} (A : BananaMatrixStructure l r)
    (c d : F2) (x : Fin l → F2) (y : Fin r → F2) :
    A.eval (c • x) (d • y) = (c * d) * A.eval x y := by
  simp [BananaMatrixStructure.eval, Matrix.mulVec_smul,
    smul_dotProduct, dotProduct_smul, smul_smul,
    mul_assoc, mul_comm, mul_left_comm]

/-- Every four-element BANANA line-pair copy induces a structural embedding
of its one-dimensional source. -/
def BananaLinePairCopy.toSourceEmbedding
    {l r : ℕ} {A : BananaMatrixStructure l r}
    {b : F2} (P : BananaLinePairCopy A b) :
    BananaMatrixEmbedding (linePairSource b) A where
  left := linePairSpanMap P.left
  right := linePairSpanMap P.right
  left_injective := linePairSpanMap_injective P.left_ne_zero
  right_injective := linePairSpanMap_injective P.right_ne_zero
  pairing_apply := by
    intro u v
    change
      A.eval (linePairSpanMap P.left u) (linePairSpanMap P.right v) =
        (linePairSource b).eval u v
    rw [linePairSpanMap_apply, linePairSpanMap_apply,
      A.eval_smul_smul, P.pairing, linePairSource_eval]

/-- The source basis vectors are sent to the two vectors recording the
line-pair copy. -/
@[simp] theorem BananaLinePairCopy.toSourceEmbedding_left_basis
    {l r : ℕ} {A : BananaMatrixStructure l r}
    {b : F2} (P : BananaLinePairCopy A b) :
    (P.toSourceEmbedding).left (Pi.single (0 : Fin 1) 1) = P.left := by
  simp [BananaLinePairCopy.toSourceEmbedding, linePairSpanMap]

@[simp] theorem BananaLinePairCopy.toSourceEmbedding_right_basis
    {l r : ℕ} {A : BananaMatrixStructure l r}
    {b : F2} (P : BananaLinePairCopy A b) :
    (P.toSourceEmbedding).right (Pi.single (0 : Fin 1) 1) = P.right := by
  simp [BananaLinePairCopy.toSourceEmbedding, linePairSpanMap]

end SuccessorTree.NonPrecompact
