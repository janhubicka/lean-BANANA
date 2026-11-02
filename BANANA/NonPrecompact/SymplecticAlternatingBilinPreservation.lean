import BANANA.NonPrecompact.SymplecticAlternatingStrongAmalgam
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# Full-vector pairing preservation for the alternating block amalgam

The matrix-amalgamation lemma proved previously checks matrix entries
in selected basis coordinates.  This module checks preservation of the
ACTUAL bilinear forms on all vectors, using Mathlib's matrix-to-bilinear
equivalence and its explicit double-sum formula.

The source inclusions are the F₂-linear maps
  u(a,x) ↦ (a,x,0),    v(a,y) ↦ (a,0,y).
The only nonzero terms of each double sum lie in the corresponding
source block, where the amalgam matrix agrees with the source matrix.

The result is for diagrams with common A coordinates; a reduction of
arbitrary injective linear isometries to a common chosen basis remains
to be proved before claiming a full Fraïssé amalgamation interface.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical BigOperators

/-- Preservation of the left bilinear pairing on arbitrary vectors.
No alternation or nondegeneracy assumption is needed for this identity. -/
theorem symplecticBlockVectorLeft_pairing
    {A X Y : Type*}
    [Fintype A] [Fintype X] [Fintype Y]
    (B : Matrix (Sum A X) (Sum A X) F2)
    (C : Matrix (Sum A Y) (Sum A Y) F2)
    (u v : Sum A X → F2) :
    (Matrix.toBilin' (symplecticBlockAmalgam B C))
      (symplecticBlockVectorLeft u)
      (symplecticBlockVectorLeft v) =
    (Matrix.toBilin' B) u v := by
  classical
  simp only [Matrix.toBilin'_apply]
  simp [Fintype.sum_sum_type,
    symplecticBlockVectorLeft, symplecticBlockAmalgam,
    add_assoc, add_left_comm, add_comm]

/-- Preservation of the right bilinear pairing on arbitrary vectors
requires agreement of the old matrices on the shared A-by-A block. -/
theorem symplecticBlockVectorRight_pairing
    {A X Y : Type*}
    [Fintype A] [Fintype X] [Fintype Y]
    (B : Matrix (Sum A X) (Sum A X) F2)
    (C : Matrix (Sum A Y) (Sum A Y) F2)
    (hcommon : ∀ a a',
      B (.inl a) (.inl a') = C (.inl a) (.inl a'))
    (u v : Sum A Y → F2) :
    (Matrix.toBilin' (symplecticBlockAmalgam B C))
      (symplecticBlockVectorRight u)
      (symplecticBlockVectorRight v) =
    (Matrix.toBilin' C) u v := by
  classical
  simp only [Matrix.toBilin'_apply]
  simp [Fintype.sum_sum_type,
    symplecticBlockVectorRight, symplecticBlockAmalgam,
    hcommon, add_assoc, add_left_comm, add_comm]

/-- A complete strong coordinate *vector-space* amalgam of alternating
binary bilinear forms. The inclusion maps preserve both original
bilinear forms on all pairs of vectors, in addition to injectivity
and exact image intersection. In particular the two full-vector
pairing identities do not rely on nondegeneracy.

This certificate remains conditional on having chosen bases which
identify the two embeddings of the common subspace with the displayed
A-block inclusions. -/
theorem symplecticAlternatingBlock_exists_fullVectorAmalgam
    {A X Y : Type*}
    [Fintype A] [Fintype X] [Fintype Y]
    (B : Matrix (Sum A X) (Sum A X) F2)
    (C : Matrix (Sum A Y) (Sum A Y) F2)
    (hcommon : ∀ a a',
      B (.inl a) (.inl a') = C (.inl a) (.inl a'))
    (hBdiag : ∀ i, B i i = 0)
    (hCdiag : ∀ i, C i i = 0)
    (hBsymm : ∀ i j, B i j = B j i)
    (hCsymm : ∀ i j, C i j = C j i) :
    ∃ D : Matrix (Sum A (Sum X Y)) (Sum A (Sum X Y)) F2,
      (∀ i, D i i = 0) ∧
      (∀ i j, D i j = D j i) ∧
      Function.Injective (symplecticBlockVectorLeft (A := A) (X := X) (Y := Y)) ∧
      Function.Injective (symplecticBlockVectorRight (A := A) (X := X) (Y := Y)) ∧
      (∀ (u : Sum A X → F2) (v : Sum A Y → F2),
        symplecticBlockVectorLeft u = symplecticBlockVectorRight v ↔
          ∃ w : A → F2,
            u = symplecticBlockVectorCommonLeft w ∧
            v = symplecticBlockVectorCommonRight w) ∧
      (∀ u v : Sum A X → F2,
        (Matrix.toBilin' D)
          (symplecticBlockVectorLeft u)
          (symplecticBlockVectorLeft v) = (Matrix.toBilin' B) u v) ∧
      (∀ u v : Sum A Y → F2,
        (Matrix.toBilin' D)
          (symplecticBlockVectorRight u)
          (symplecticBlockVectorRight v) = (Matrix.toBilin' C) u v) := by
  refine ⟨symplecticBlockAmalgam B C,
    symplecticBlockAmalgam_diag_zero B C hBdiag hCdiag,
    symplecticBlockAmalgam_symmetric B C hBsymm hCsymm,
    symplecticBlockVectorLeft_injective,
    symplecticBlockVectorRight_injective,
    symplecticBlockVector_intersection,
    ?_, ?_⟩
  · intro u v
    exact symplecticBlockVectorLeft_pairing B C u v
  · intro u v
    exact symplecticBlockVectorRight_pairing B C hcommon u v

end SuccessorTree.NonPrecompact
