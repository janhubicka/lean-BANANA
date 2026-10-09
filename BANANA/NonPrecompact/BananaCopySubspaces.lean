import BANANA.NonPrecompact.BananaCopyRanges
import BANANA.NonPrecompact.BinarySubspaceRamseyInterface

/-!
# Finite subspaces underlying unlabelled BANANA copies

The one-sided degree-one reduction in the circulation manuscript colours
unlabelled copies.  The binary GLR interface instead colours subspaces.
This module makes the range identification and its functoriality explicit.

The two projected subspaces are defined for arbitrary BANANA copies; the
uniqueness results use the assumption that the other sort is zero.
Nothing here assumes a Ramsey theorem.
-/

namespace SuccessorTree.NonPrecompact

open Module

/-- The left range of an unlabelled copy, equipped with its dimension. -/
noncomputable def BananaCopyRanges.leftFixedSubspace
    {a r lC rC : ℕ}
    {A : BananaMatrixStructure a r}
    {C : BananaMatrixStructure lC rC}
    (D : BananaCopyRanges A C) : FixedSubspace a lC := by
  classical
  let e : BananaMatrixEmbedding A C := Classical.choose D.property
  refine ⟨LinearMap.range e.left, ?_⟩
  rw [LinearMap.finrank_range_of_inj e.left_injective]
  simp [Module.finrank_fintype_fun_eq_card]

/-- The right range of an unlabelled copy, equipped with its dimension. -/
noncomputable def BananaCopyRanges.rightFixedSubspace
    {l a lC rC : ℕ}
    {A : BananaMatrixStructure l a}
    {C : BananaMatrixStructure lC rC}
    (D : BananaCopyRanges A C) : FixedSubspace a rC := by
  classical
  let e : BananaMatrixEmbedding A C := Classical.choose D.property
  refine ⟨LinearMap.range e.right, ?_⟩
  rw [LinearMap.finrank_range_of_inj e.right_injective]
  simp [Module.finrank_fintype_fun_eq_card]

/-- The left subspace has precisely the finite-vector range of the copy. -/
theorem BananaCopyRanges.mem_leftFixedSubspace_iff
    {a r lC rC : ℕ}
    {A : BananaMatrixStructure a r}
    {C : BananaMatrixStructure lC rC}
    (D : BananaCopyRanges A C) (z : Fin lC → F2) :
    z ∈ D.leftFixedSubspace.1 ↔ z ∈ D.1.1 := by
  classical
  let e : BananaMatrixEmbedding A C := Classical.choose D.property
  have hl : D.1.1 = Finset.univ.image e.left :=
    (Classical.choose_spec D.property).1
  change z ∈ LinearMap.range e.left ↔ z ∈ D.1.1
  rw [hl]
  constructor
  · rintro ⟨x, rfl⟩
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩
  · intro hz
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hz
    exact ⟨x, hx⟩

/-- The right subspace has precisely the finite-vector range of the copy. -/
theorem BananaCopyRanges.mem_rightFixedSubspace_iff
    {l a lC rC : ℕ}
    {A : BananaMatrixStructure l a}
    {C : BananaMatrixStructure lC rC}
    (D : BananaCopyRanges A C) (z : Fin rC → F2) :
    z ∈ D.rightFixedSubspace.1 ↔ z ∈ D.1.2 := by
  classical
  let e : BananaMatrixEmbedding A C := Classical.choose D.property
  have hr : D.1.2 = Finset.univ.image e.right :=
    (Classical.choose_spec D.property).2
  change z ∈ LinearMap.range e.right ↔ z ∈ D.1.2
  rw [hr]
  constructor
  · rintro ⟨x, rfl⟩
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩
  · intro hz
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hz
    exact ⟨x, hx⟩

/-- Taking the left subspace commutes with ambient embeddings. -/
theorem BananaCopyRanges.leftFixedSubspace_map
    {a r lB rB lC rC : ℕ}
    {A : BananaMatrixStructure a r}
    {B : BananaMatrixStructure lB rB}
    {C : BananaMatrixStructure lC rC}
    (D : BananaCopyRanges A B)
    (f : BananaMatrixEmbedding B C) :
    (D.map f).leftFixedSubspace =
      D.leftFixedSubspace.map f.left f.left_injective := by
  classical
  apply Subtype.ext
  apply Submodule.ext
  intro z
  rw [(D.map f).mem_leftFixedSubspace_iff z]
  change z ∈ D.1.1.image f.left ↔
    z ∈ LinearMap.range (f.left.comp D.leftFixedSubspace.1.subtype)
  constructor
  · intro hz
    obtain ⟨x, hx, hfx⟩ := Finset.mem_image.mp hz
    exact ⟨⟨x, (D.mem_leftFixedSubspace_iff x).2 hx⟩, hfx⟩
  · rintro ⟨x, hfx⟩
    exact Finset.mem_image.mpr
      ⟨x.1, (D.mem_leftFixedSubspace_iff x.1).1 x.property, hfx⟩

/-- Taking the right subspace commutes with ambient embeddings. -/
theorem BananaCopyRanges.rightFixedSubspace_map
    {l a lB rB lC rC : ℕ}
    {A : BananaMatrixStructure l a}
    {B : BananaMatrixStructure lB rB}
    {C : BananaMatrixStructure lC rC}
    (D : BananaCopyRanges A B)
    (f : BananaMatrixEmbedding B C) :
    (D.map f).rightFixedSubspace =
      D.rightFixedSubspace.map f.right f.right_injective := by
  classical
  apply Subtype.ext
  apply Submodule.ext
  intro z
  rw [(D.map f).mem_rightFixedSubspace_iff z]
  change z ∈ D.1.2.image f.right ↔
    z ∈ LinearMap.range (f.right.comp D.rightFixedSubspace.1.subtype)
  constructor
  · intro hz
    obtain ⟨x, hx, hfx⟩ := Finset.mem_image.mp hz
    exact ⟨⟨x, (D.mem_rightFixedSubspace_iff x).2 hx⟩, hfx⟩
  · rintro ⟨x, hfx⟩
    exact Finset.mem_image.mpr
      ⟨x.1, (D.mem_rightFixedSubspace_iff x.1).1 x.property, hfx⟩

/-- The right range of a copy with zero-dimensional right sort is {0}. -/
theorem BananaCopyRanges.rightRange_singleton_of_rightZero
    {a lC rC : ℕ}
    {A : BananaMatrixStructure a 0}
    {C : BananaMatrixStructure lC rC}
    (D : BananaCopyRanges A C) :
    D.1.2 = {0} := by
  classical
  obtain ⟨e, _, hr⟩ := D.property
  rw [hr]
  ext z
  constructor
  · intro hz
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hz
    have hx0 : x = 0 := Subsingleton.elim x 0
    subst x
    have hz0 : z = 0 := hx.symm.trans e.right_zero
    simpa only [Finset.mem_singleton] using hz0
  · intro hz
    have hz0 : z = 0 := by simpa only [Finset.mem_singleton] using hz
    subst z
    exact Finset.mem_image.mpr
      ⟨0, Finset.mem_univ _, e.right_zero⟩

/-- The left range of a copy with zero-dimensional left sort is {0}. -/
theorem BananaCopyRanges.leftRange_singleton_of_leftZero
    {a lC rC : ℕ}
    {A : BananaMatrixStructure 0 a}
    {C : BananaMatrixStructure lC rC}
    (D : BananaCopyRanges A C) :
    D.1.1 = {0} := by
  classical
  obtain ⟨e, hl, _⟩ := D.property
  rw [hl]
  ext z
  constructor
  · intro hz
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hz
    have hx0 : x = 0 := Subsingleton.elim x 0
    subst x
    have hz0 : z = 0 := hx.symm.trans e.left_zero
    simpa only [Finset.mem_singleton] using hz0
  · intro hz
    have hz0 : z = 0 := by simpa only [Finset.mem_singleton] using hz
    subst z
    exact Finset.mem_image.mpr
      ⟨0, Finset.mem_univ _, e.left_zero⟩

/-- For a left-only source the unlabelled copy is determined by its left
subspace, without any choice of a source isomorphism. -/
theorem BananaCopyRanges.ext_of_leftFixedSubspace_eq
    {a lC rC : ℕ}
    {A : BananaMatrixStructure a 0}
    {C : BananaMatrixStructure lC rC}
    {D E : BananaCopyRanges A C}
    (h : D.leftFixedSubspace = E.leftFixedSubspace) :
    D = E := by
  apply Subtype.ext
  apply Prod.ext
  · ext z
    change z ∈ D.1.1 ↔ z ∈ E.1.1
    rw [← D.mem_leftFixedSubspace_iff z,
        ← E.mem_leftFixedSubspace_iff z, h]
  · exact D.rightRange_singleton_of_rightZero.trans
      E.rightRange_singleton_of_rightZero.symm

/-- Symmetrically, a right-only copy is determined by its right subspace. -/
theorem BananaCopyRanges.ext_of_rightFixedSubspace_eq
    {a lC rC : ℕ}
    {A : BananaMatrixStructure 0 a}
    {C : BananaMatrixStructure lC rC}
    {D E : BananaCopyRanges A C}
    (h : D.rightFixedSubspace = E.rightFixedSubspace) :
    D = E := by
  apply Subtype.ext
  apply Prod.ext
  · exact D.leftRange_singleton_of_leftZero.trans
      E.leftRange_singleton_of_leftZero.symm
  · ext z
    change z ∈ D.1.2 ↔ z ∈ E.1.2
    rw [← D.mem_rightFixedSubspace_iff z,
        ← E.mem_rightFixedSubspace_iff z, h]

end SuccessorTree.NonPrecompact
