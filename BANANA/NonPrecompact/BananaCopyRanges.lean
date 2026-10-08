import BANANA.NonPrecompact.BananaEmbeddingDegree
import Mathlib.Data.Finset.Image

/-!
# Unlabelled copies of finite BANANA structures

For a fixed source `A`, an unlabelled copy in `C` is determined by
the two *ranges* of an embedding of `A`. Since the pairing on those
ranges is inherited from `C`, no labels or distinguished bases belong
to the copy. In particular, changing the embedding by an automorphism
of `A` does not change the copy.

This representation makes the distinction between the manuscript's
copy Ramsey degree and the embedding Ramsey degree explicit.
-/

namespace SuccessorTree.NonPrecompact

/-- An unlabelled copy of `A` in `C`, recorded by its two finite
vector-space ranges. The existence proof ensures that the restrictions
of the ambient pairing are isomorphic to the pairing of `A`. -/
abbrev BananaCopyRanges
    {l r lC rC : ℕ}
    (A : BananaMatrixStructure l r)
    (C : BananaMatrixStructure lC rC) :=
  { ranges :
      Finset (Fin lC → F2) × Finset (Fin rC → F2) //
    ∃ e : BananaMatrixEmbedding A C,
      ranges.1 = Finset.univ.image e.left ∧
      ranges.2 = Finset.univ.image e.right }

/-- Every pair of injective pairing-preserving maps defines an
unlabelled copy by taking the two images. -/
noncomputable def BananaMatrixEmbedding.copyRanges
    {l r lC rC : ℕ}
    {A : BananaMatrixStructure l r}
    {C : BananaMatrixStructure lC rC}
    (e : BananaMatrixEmbedding A C) :
    BananaCopyRanges A C := by
  classical
  exact ⟨(Finset.univ.image e.left, Finset.univ.image e.right),
    ⟨e, rfl, rfl⟩⟩

/-- A copy is moved by an ambient embedding simply by taking the
images of its two ranges. This is independent of the chosen
representation of the original copy. -/
noncomputable def BananaCopyRanges.map
    {l r lB rB lC rC : ℕ}
    {A : BananaMatrixStructure l r}
    {B : BananaMatrixStructure lB rB}
    {C : BananaMatrixStructure lC rC}
    (D : BananaCopyRanges A B)
    (f : BananaMatrixEmbedding B C) :
    BananaCopyRanges A C := by
  classical
  refine ⟨(D.1.1.image f.left, D.1.2.image f.right), ?_⟩
  obtain ⟨e, hleft, hright⟩ := D.property
  refine ⟨BananaMatrixEmbedding.comp f e, ?_, ?_⟩
  · change D.1.1.image f.left =
      Finset.univ.image ((BananaMatrixEmbedding.comp f e).left)
    rw [hleft, Finset.image_image]
    rfl
  · change D.1.2.image f.right =
      Finset.univ.image ((BananaMatrixEmbedding.comp f e).right)
    rw [hright, Finset.image_image]
    rfl

/-- Taking ranges commutes with composing structural embeddings. -/
@[simp] theorem BananaMatrixEmbedding.copyRanges_comp
    {l r lB rB lC rC : ℕ}
    {A : BananaMatrixStructure l r}
    {B : BananaMatrixStructure lB rB}
    {C : BananaMatrixStructure lC rC}
    (e : BananaMatrixEmbedding A B)
    (f : BananaMatrixEmbedding B C) :
    e.copyRanges.map f =
      (BananaMatrixEmbedding.comp f e).copyRanges := by
  classical
  apply Subtype.ext
  apply Prod.ext
  · change (Finset.univ.image e.left).image f.left =
      Finset.univ.image ((BananaMatrixEmbedding.comp f e).left)
    rw [Finset.image_image]
    rfl
  · change (Finset.univ.image e.right).image f.right =
      Finset.univ.image ((BananaMatrixEmbedding.comp f e).right)
    rw [Finset.image_image]
    rfl

/-- All unlabelled copies in a finite BANANA structure form a
finite type, unlike the corresponding infinite Fraïssé limit. -/
noncomputable instance bananaCopyRangesFintype
    {l r lC rC : ℕ}
    (A : BananaMatrixStructure l r)
    (C : BananaMatrixStructure lC rC) :
    Fintype (BananaCopyRanges A C) := by
  classical
  infer_instance

/-- A line-pair copy lies inside an unlabelled copy when its
two generating vectors belong to the respective ranges. -/
def BananaLinePairCopy.InCopy
    {l r lC rC : ℕ}
    {A : BananaMatrixStructure l r}
    {C : BananaMatrixStructure lC rC}
    {b : F2}
    (P : BananaLinePairCopy C b)
    (D : BananaCopyRanges A C) : Prop :=
  P.left ∈ D.1.1 ∧ P.right ∈ D.1.2

/-- The line pair singled out by an embedding of the four-element
source lies in the corresponding unlabelled copy of the full source. -/
theorem BananaMatrixEmbedding.toLinePairCopy_in_copyRanges
    {l r lC rC : ℕ}
    {A : BananaMatrixStructure l r}
    {C : BananaMatrixStructure lC rC}
    {b : F2}
    (e : BananaMatrixEmbedding A C)
    (i : BananaMatrixEmbedding (linePairSource b) A) :
    (BananaMatrixEmbedding.comp e i).toLinePairCopy.InCopy
      e.copyRanges := by
  classical
  constructor
  · change (BananaMatrixEmbedding.comp e i).toLinePairCopy.left ∈
      Finset.univ.image e.left
    rw [BananaMatrixEmbedding.toLinePairCopy_comp]
    exact Finset.mem_image.mpr
      ⟨i.toLinePairCopy.left, Finset.mem_univ _, rfl⟩
  · change (BananaMatrixEmbedding.comp e i).toLinePairCopy.right ∈
      Finset.univ.image e.right
    rw [BananaMatrixEmbedding.toLinePairCopy_comp]
    exact Finset.mem_image.mpr
      ⟨i.toLinePairCopy.right, Finset.mem_univ _, rfl⟩

/-- Containment of a line pair in an unlabelled copy is preserved
under every ambient embedding. -/
theorem BananaLinePairCopy.InCopy.map
    {l r lB rB lC rC : ℕ}
    {A : BananaMatrixStructure l r}
    {B : BananaMatrixStructure lB rB}
    {C : BananaMatrixStructure lC rC}
    {b : F2}
    {P : BananaLinePairCopy B b}
    {D : BananaCopyRanges A B}
    (h : P.InCopy D)
    (f : BananaMatrixEmbedding B C) :
    (f.mapLinePairCopy P).InCopy (D.map f) := by
  classical
  constructor
  · change f.left P.left ∈ D.1.1.image f.left
    exact Finset.mem_image.mpr ⟨P.left, h.1, rfl⟩
  · change f.right P.right ∈ D.1.2.image f.right
    exact Finset.mem_image.mpr ⟨P.right, h.2, rfl⟩

/-- A line pair contained in the two ranges of an embedding has a
unique preimage pair of vectors; injectivity and pairing preservation
make that preimage a line-pair copy of the source. -/
theorem BananaMatrixEmbedding.exists_linePair_preimage
    {l r lC rC : ℕ}
    {A : BananaMatrixStructure l r}
    {C : BananaMatrixStructure lC rC}
    {b : F2}
    (e : BananaMatrixEmbedding A C)
    (P : BananaLinePairCopy C b)
    (h : P.InCopy e.copyRanges) :
    ∃ Q : BananaLinePairCopy A b, e.mapLinePairCopy Q = P := by
  classical
  change P.left ∈ Finset.univ.image e.left ∧
    P.right ∈ Finset.univ.image e.right at h
  obtain ⟨x, _, hx⟩ := Finset.mem_image.mp h.1
  obtain ⟨y, _, hy⟩ := Finset.mem_image.mp h.2
  have hxne : x ≠ 0 := by
    intro hzero
    apply P.left_ne_zero
    calc
      P.left = e.left x := hx.symm
      _ = e.left 0 := by rw [hzero]
      _ = 0 := e.left_zero
  have hyne : y ≠ 0 := by
    intro hzero
    apply P.right_ne_zero
    calc
      P.right = e.right y := hy.symm
      _ = e.right 0 := by rw [hzero]
      _ = 0 := e.right_zero
  have hp : A.eval x y = b := by
    calc
      A.eval x y = C.eval (e.left x) (e.right y) :=
        (e.pairing_apply x y).symm
      _ = b := by rw [hx, hy]; exact P.pairing
  let Q : BananaLinePairCopy A b := ⟨x, y, hxne, hyne, hp⟩
  refine ⟨Q, ?_⟩
  apply BananaLinePairCopy.eq_of_vectors
  · exact hx
  · exact hy

end SuccessorTree.NonPrecompact
