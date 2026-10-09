import BANANA.NonPrecompact.BananaCopyDegree
import BANANA.NonPrecompact.LinearBinaryRepresentability

/-!
# Subspace descriptions of one-sided unlabelled BANANA copies

A copy of a BANANA source whose right sort is zero is completely
specified by its left image subspace. The analogous statement holds
for a source whose left sort is zero. We give both descriptions and
check functoriality under embeddings of the ambient structures.

These are the representation lemmas needed to transport the
already formalised unconditional binary GLR Ramsey theorem to the
unlabelled-copy notion `BananaCopyRanges`.

This file is staged for a local Lean kernel build: the root package
must not import it until that build succeeds.
-/

namespace SuccessorTree.NonPrecompact

open LinearMap Module

/-- All vectors of the zero-dimensional binary space coincide. -/
private theorem zeroCoordinates_eq_zero (x : Fin 0 → F2) : x = 0 := by
  funext i
  exact Fin.elim0 i

/-- The image of the zero-dimensional space under any linear map is
the singleton consisting of zero. -/
private theorem image_zeroCoordinates
    {n : ℕ}
    (f : (Fin 0 → F2) →ₗ[F2] (Fin n → F2)) :
    (Finset.univ : Finset (Fin 0 → F2)).image f = {0} := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hz
    rw [zeroCoordinates_eq_zero x, f.map_zero] at hx
    exact Finset.mem_singleton.mpr hx.symm
  · intro hz
    have hz0 : z = 0 := Finset.mem_singleton.mp hz
    subst z
    exact Finset.mem_image.mpr
      ⟨0, Finset.mem_univ _, by simp⟩

/-- The left image subspace of an unlabelled copy of a left-only
source, of exactly the source's dimension. -/
noncomputable def BananaCopyRanges.leftFixedSubspace
    {a n m : ℕ}
    {A : BananaMatrixStructure a 0}
    {C : BananaMatrixStructure n m}
    (D : BananaCopyRanges A C) : FixedSubspace a n := by
  classical
  let e := Classical.choose D.property
  refine ⟨LinearMap.range e.left, ?_⟩
  have hfin := LinearMap.finrank_range_of_inj e.left_injective
  simpa [Module.finrank_fintype_fun_eq_card] using hfin

/-- Membership in the left image subspace is independent of the
chosen embedding representing an unlabelled copy. -/
theorem BananaCopyRanges.mem_leftFixedSubspace_iff
    {a n m : ℕ}
    {A : BananaMatrixStructure a 0}
    {C : BananaMatrixStructure n m}
    (D : BananaCopyRanges A C) (x : Fin n → F2) :
    x ∈ D.leftFixedSubspace.1 ↔ x ∈ D.1.1 := by
  classical
  let e := Classical.choose D.property
  have hleft : D.1.1 = Finset.univ.image e.left :=
    (Classical.choose_spec D.property).1
  change x ∈ LinearMap.range e.left ↔ x ∈ D.1.1
  rw [hleft]
  constructor
  · rintro ⟨y, hy⟩
    exact Finset.mem_image.mpr
      ⟨y, Finset.mem_univ _, hy⟩
  · intro hx
    obtain ⟨y, _, hy⟩ := Finset.mem_image.mp hx
    exact ⟨y, hy⟩

/-- The right image of a copy of a left-only source is exactly zero. -/
theorem BananaCopyRanges.leftOnly_rightRange
    {a n m : ℕ}
    {A : BananaMatrixStructure a 0}
    {C : BananaMatrixStructure n m}
    (D : BananaCopyRanges A C) :
    D.1.2 = ({0} : Finset (Fin m → F2)) := by
  classical
  obtain ⟨e, _, hright⟩ := D.property
  rw [hright]
  exact image_zeroCoordinates e.right

/-- Two left-only unlabelled copies with the same left subspace
are equal, regardless of their parametrisations. -/
theorem BananaCopyRanges.leftFixedSubspace_injective
    {a n m : ℕ}
    {A : BananaMatrixStructure a 0}
    {C : BananaMatrixStructure n m} :
    Function.Injective
      (fun D : BananaCopyRanges A C => D.leftFixedSubspace) := by
  intro D E h
  apply Subtype.ext
  apply Prod.ext
  · ext x
    have heq : x ∈ D.leftFixedSubspace.1 ↔
        x ∈ E.leftFixedSubspace.1 := by
      rw [h]
    exact (D.mem_leftFixedSubspace_iff x).symm.trans
      (heq.trans (E.mem_leftFixedSubspace_iff x))
  · rw [D.leftOnly_rightRange, E.leftOnly_rightRange]

/-- Mapping a left-only copy into another BANANA structure transports
its associated subspace by the ambient left linear map. -/
theorem BananaCopyRanges.leftFixedSubspace_map
    {a lB rB lC rC : ℕ}
    {A : BananaMatrixStructure a 0}
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
  constructor
  · intro hz
    have hm : z ∈ (D.map f).1.1 :=
      ((D.map f).mem_leftFixedSubspace_iff z).mp hz
    change z ∈ D.1.1.image f.left at hm
    obtain ⟨x, hx, hxz⟩ := Finset.mem_image.mp hm
    change z ∈ LinearMap.range
      (f.left.comp D.leftFixedSubspace.1.subtype)
    exact ⟨⟨x, (D.mem_leftFixedSubspace_iff x).mpr hx⟩, hxz⟩
  · intro hz
    change z ∈ LinearMap.range
      (f.left.comp D.leftFixedSubspace.1.subtype) at hz
    obtain ⟨x, hx⟩ := hz
    have hxmem : (x : Fin lB → F2) ∈ D.1.1 :=
      (D.mem_leftFixedSubspace_iff x).mp x.property
    apply ((D.map f).mem_leftFixedSubspace_iff z).mpr
    change z ∈ D.1.1.image f.left
    exact Finset.mem_image.mpr ⟨x, hxmem, hx⟩

/-- The right image subspace of an unlabelled copy whose left
sort is zero. -/
noncomputable def BananaCopyRanges.rightFixedSubspace
    {a n m : ℕ}
    {A : BananaMatrixStructure 0 a}
    {C : BananaMatrixStructure n m}
    (D : BananaCopyRanges A C) : FixedSubspace a m := by
  classical
  let e := Classical.choose D.property
  refine ⟨LinearMap.range e.right, ?_⟩
  have hfin := LinearMap.finrank_range_of_inj e.right_injective
  simpa [Module.finrank_fintype_fun_eq_card] using hfin

/-- Membership in the right image subspace depends only on the copy. -/
theorem BananaCopyRanges.mem_rightFixedSubspace_iff
    {a n m : ℕ}
    {A : BananaMatrixStructure 0 a}
    {C : BananaMatrixStructure n m}
    (D : BananaCopyRanges A C) (y : Fin m → F2) :
    y ∈ D.rightFixedSubspace.1 ↔ y ∈ D.1.2 := by
  classical
  let e := Classical.choose D.property
  have hright : D.1.2 = Finset.univ.image e.right :=
    (Classical.choose_spec D.property).2
  change y ∈ LinearMap.range e.right ↔ y ∈ D.1.2
  rw [hright]
  constructor
  · rintro ⟨x, hx⟩
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, hx⟩
  · intro hy
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hy
    exact ⟨x, hx⟩

/-- The left range of a copy of a right-only source is the zero space. -/
theorem BananaCopyRanges.rightOnly_leftRange
    {a n m : ℕ}
    {A : BananaMatrixStructure 0 a}
    {C : BananaMatrixStructure n m}
    (D : BananaCopyRanges A C) :
    D.1.1 = ({0} : Finset (Fin n → F2)) := by
  classical
  obtain ⟨e, hleft, _⟩ := D.property
  rw [hleft]
  exact image_zeroCoordinates e.left

/-- A right-only copy is completely specified by its right subspace. -/
theorem BananaCopyRanges.rightFixedSubspace_injective
    {a n m : ℕ}
    {A : BananaMatrixStructure 0 a}
    {C : BananaMatrixStructure n m} :
    Function.Injective
      (fun D : BananaCopyRanges A C => D.rightFixedSubspace) := by
  intro D E h
  apply Subtype.ext
  apply Prod.ext
  · rw [D.rightOnly_leftRange, E.rightOnly_leftRange]
  · ext y
    have heq : y ∈ D.rightFixedSubspace.1 ↔
        y ∈ E.rightFixedSubspace.1 := by
      rw [h]
    exact (D.mem_rightFixedSubspace_iff y).symm.trans
      (heq.trans (E.mem_rightFixedSubspace_iff y))

/-- The right-subspace description also commutes with embeddings. -/
theorem BananaCopyRanges.rightFixedSubspace_map
    {a lB rB lC rC : ℕ}
    {A : BananaMatrixStructure 0 a}
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
  constructor
  · intro hz
    have hm : z ∈ (D.map f).1.2 :=
      ((D.map f).mem_rightFixedSubspace_iff z).mp hz
    change z ∈ D.1.2.image f.right at hm
    obtain ⟨x, hx, hxz⟩ := Finset.mem_image.mp hm
    change z ∈ LinearMap.range
      (f.right.comp D.rightFixedSubspace.1.subtype)
    exact ⟨⟨x, (D.mem_rightFixedSubspace_iff x).mpr hx⟩, hxz⟩
  · intro hz
    change z ∈ LinearMap.range
      (f.right.comp D.rightFixedSubspace.1.subtype) at hz
    obtain ⟨x, hx⟩ := hz
    have hxmem : (x : Fin rB → F2) ∈ D.1.2 :=
      (D.mem_rightFixedSubspace_iff x).mp x.property
    apply ((D.map f).mem_rightFixedSubspace_iff z).mpr
    change z ∈ D.1.2.image f.right
    exact Finset.mem_image.mpr ⟨x, hxmem, hx⟩

end SuccessorTree.NonPrecompact
