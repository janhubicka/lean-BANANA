import BANANA.NonPrecompact.BananaOneSidedCopyDegree

/-!
# One-sided BANANA copies and finite binary subspaces

The degree-one proof in `BananaOneSidedCopyDegree` needs only the
injection from unlabelled copies into fixed-dimensional subspaces:
colourings extend by a default colour outside the image. In every
ambient BANANA structure, however, the injection is also surjective.

This file records the stronger equivalence explicitly. It is useful for
auditing that the copy representation has no omitted structures and for
future Ramsey arguments involving all subspaces rather than only those
currently realised as copies.

The sources and targets are finite-dimensional over F₂. In each
one-sided source, the pairing vanishes automatically, so choosing any
linear embedding on its nonzero sort and the unique map on the zero
sort gives a BANANA embedding.
-/

namespace SuccessorTree.NonPrecompact

open LinearMap Module

/-- In a zero-dimensional binary coordinate space any two vectors
coincide. No `Subsingleton` instance is needed. -/
private theorem zeroSort_ext (x y : Fin 0 → F2) : x = y := by
  funext i
  exact Fin.elim0 i

/-- Every fixed-dimensional left subspace of an arbitrary ambient BANANA
structure is the image of an unlabelled copy of any left-only source
of that dimension. -/
theorem BananaMatrixStructure.exists_leftOnlyCopy_overSubspace
    {a n m : ℕ} (A : BananaMatrixStructure a 0)
    (C : BananaMatrixStructure n m)
    (W : FixedSubspace a n) :
    ∃ D : BananaCopyRanges A C,
      D.leftFixedSubspace = W := by
  classical
  have hdim :
      finrank F2 (Fin a → F2) = finrank F2 W.1 := by
    calc
      finrank F2 (Fin a → F2) = a := by
        simp [Module.finrank_fintype_fun_eq_card]
      _ = finrank F2 W.1 := W.2.symm
  let e : (Fin a → F2) ≃ₗ[F2] W.1 :=
    LinearEquiv.ofFinrankEq (Fin a → F2) W.1 hdim
  let leftMap : (Fin a → F2) →ₗ[F2] (Fin n → F2) :=
    W.1.subtype.comp e.toLinearMap
  have hleft : Function.Injective leftMap :=
    W.1.injective_subtype.comp e.injective
  let f : BananaMatrixEmbedding A C :=
    { left := leftMap
      right := 0
      left_injective := hleft
      right_injective := by
        intro x y _
        exact zeroSort_ext x y
      pairing_apply := by
        intro x y
        have hy : y = 0 := zeroSort_ext y 0
        subst y
        simp [BananaMatrixStructure.eval] }
  refine ⟨f.copyRanges, ?_⟩
  apply Subtype.ext
  apply Submodule.ext
  intro z
  rw [f.copyRanges.mem_leftFixedSubspace_iff z]
  change z ∈ Finset.univ.image f.left ↔ z ∈ W.1
  constructor
  · intro hz
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hz
    have hmember : leftMap x ∈ W.1 := (e x).property
    have hmap : leftMap x = z := hx
    rw [hmap] at hmember
    exact hmember
  · intro hz
    obtain ⟨x, hx⟩ := e.surjective ⟨z, hz⟩
    apply Finset.mem_image.mpr
    refine ⟨x, Finset.mem_univ _, ?_⟩
    change leftMap x = z
    exact congrArg Subtype.val hx

/-- A chosen unlabelled copy over a specified left subspace. The
choice is immaterial to the copy, by
`BananaCopyRanges.leftFixedSubspace_injective`. -/
noncomputable def BananaMatrixStructure.leftOnlyCopyOfSubspace
    {a n m : ℕ} (A : BananaMatrixStructure a 0)
    (C : BananaMatrixStructure n m)
    (W : FixedSubspace a n) :
    BananaCopyRanges A C :=
  Classical.choose (A.exists_leftOnlyCopy_overSubspace C W)

@[simp] theorem BananaMatrixStructure.leftOnlyCopyOfSubspace_range
    {a n m : ℕ} (A : BananaMatrixStructure a 0)
    (C : BananaMatrixStructure n m)
    (W : FixedSubspace a n) :
    (A.leftOnlyCopyOfSubspace C W).leftFixedSubspace = W :=
  Classical.choose_spec (A.exists_leftOnlyCopy_overSubspace C W)

/-- In arbitrary BANANA structures, taking the left image subspace gives
a bijection from unlabelled left-only copies to fixed-dimensional
subspaces. -/
noncomputable def BananaMatrixStructure.leftOnlyCopySubspaceEquiv
    {a n m : ℕ} (A : BananaMatrixStructure a 0)
    (C : BananaMatrixStructure n m) :
    BananaCopyRanges A C ≃ FixedSubspace a n where
  toFun := fun D => D.leftFixedSubspace
  invFun := A.leftOnlyCopyOfSubspace C
  left_inv := by
    intro D
    apply BananaCopyRanges.leftFixedSubspace_injective
    exact A.leftOnlyCopyOfSubspace_range C D.leftFixedSubspace
  right_inv := A.leftOnlyCopyOfSubspace_range C

/-- Every fixed-dimensional right subspace of an arbitrary ambient
pairing is the image of a copy of any right-only source. -/
theorem BananaMatrixStructure.exists_rightOnlyCopy_overSubspace
    {a n m : ℕ} (A : BananaMatrixStructure 0 a)
    (C : BananaMatrixStructure n m)
    (W : FixedSubspace a m) :
    ∃ D : BananaCopyRanges A C,
      D.rightFixedSubspace = W := by
  classical
  have hdim :
      finrank F2 (Fin a → F2) = finrank F2 W.1 := by
    calc
      finrank F2 (Fin a → F2) = a := by
        simp [Module.finrank_fintype_fun_eq_card]
      _ = finrank F2 W.1 := W.2.symm
  let e : (Fin a → F2) ≃ₗ[F2] W.1 :=
    LinearEquiv.ofFinrankEq (Fin a → F2) W.1 hdim
  let rightMap : (Fin a → F2) →ₗ[F2] (Fin m → F2) :=
    W.1.subtype.comp e.toLinearMap
  have hright : Function.Injective rightMap :=
    W.1.injective_subtype.comp e.injective
  let f : BananaMatrixEmbedding A C :=
    { left := 0
      right := rightMap
      left_injective := by
        intro x y _
        exact zeroSort_ext x y
      right_injective := hright
      pairing_apply := by
        intro x y
        have hx : x = 0 := zeroSort_ext x 0
        subst x
        simp [BananaMatrixStructure.eval] }
  refine ⟨f.copyRanges, ?_⟩
  apply Subtype.ext
  apply Submodule.ext
  intro z
  rw [f.copyRanges.mem_rightFixedSubspace_iff z]
  change z ∈ Finset.univ.image f.right ↔ z ∈ W.1
  constructor
  · intro hz
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hz
    have hmember : rightMap x ∈ W.1 := (e x).property
    have hmap : rightMap x = z := hx
    rw [hmap] at hmember
    exact hmember
  · intro hz
    obtain ⟨x, hx⟩ := e.surjective ⟨z, hz⟩
    apply Finset.mem_image.mpr
    refine ⟨x, Finset.mem_univ _, ?_⟩
    change rightMap x = z
    exact congrArg Subtype.val hx

/-- A canonical-for-the-proof unlabelled copy over a right subspace. -/
noncomputable def BananaMatrixStructure.rightOnlyCopyOfSubspace
    {a n m : ℕ} (A : BananaMatrixStructure 0 a)
    (C : BananaMatrixStructure n m)
    (W : FixedSubspace a m) :
    BananaCopyRanges A C :=
  Classical.choose (A.exists_rightOnlyCopy_overSubspace C W)

@[simp] theorem BananaMatrixStructure.rightOnlyCopyOfSubspace_range
    {a n m : ℕ} (A : BananaMatrixStructure 0 a)
    (C : BananaMatrixStructure n m)
    (W : FixedSubspace a m) :
    (A.rightOnlyCopyOfSubspace C W).rightFixedSubspace = W :=
  Classical.choose_spec (A.exists_rightOnlyCopy_overSubspace C W)

/-- The symmetric equivalence between right-only copies and
fixed-dimensional right subspaces in arbitrary ambient structures. -/
noncomputable def BananaMatrixStructure.rightOnlyCopySubspaceEquiv
    {a n m : ℕ} (A : BananaMatrixStructure 0 a)
    (C : BananaMatrixStructure n m) :
    BananaCopyRanges A C ≃ FixedSubspace a m where
  toFun := fun D => D.rightFixedSubspace
  invFun := A.rightOnlyCopyOfSubspace C
  left_inv := by
    intro D
    apply BananaCopyRanges.rightFixedSubspace_injective
    exact A.rightOnlyCopyOfSubspace_range C D.rightFixedSubspace
  right_inv := A.rightOnlyCopyOfSubspace_range C

end SuccessorTree.NonPrecompact
