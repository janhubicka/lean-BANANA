import BANANA.NonPrecompact.BananaOneSidedCopyDegree

/-!
# One-sided BANANA copies and finite binary subspaces

The degree-one proof in `BananaOneSidedCopyDegree` needs only the
injection from unlabelled copies into fixed-dimensional subspaces:
colourings extend by a default colour outside the image. In a standard
perfect pairing, however, the injection is also surjective.

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

/-- Every fixed-dimensional left subspace of a standard perfect pairing
is the image of an unlabelled copy of any left-only source of that
dimension. -/
theorem BananaMatrixStructure.exists_leftOnlyCopy_overSubspace
    {a n : ℕ} (A : BananaMatrixStructure a 0)
    (W : FixedSubspace a n) :
    ∃ D : BananaCopyRanges A (perfectBanana n),
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
  let f : BananaMatrixEmbedding A (perfectBanana n) :=
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
    rw [hx] at hmember
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
    {a n : ℕ} (A : BananaMatrixStructure a 0)
    (W : FixedSubspace a n) :
    BananaCopyRanges A (perfectBanana n) :=
  Classical.choose (A.exists_leftOnlyCopy_overSubspace W)

@[simp] theorem BananaMatrixStructure.leftOnlyCopyOfSubspace_range
    {a n : ℕ} (A : BananaMatrixStructure a 0)
    (W : FixedSubspace a n) :
    (A.leftOnlyCopyOfSubspace W).leftFixedSubspace = W :=
  Classical.choose_spec (A.exists_leftOnlyCopy_overSubspace W)

/-- In standard perfect pairings, taking the left image subspace gives
a bijection from unlabelled left-only copies to fixed-dimensional
subspaces. -/
noncomputable def BananaMatrixStructure.leftOnlyCopySubspaceEquiv
    {a n : ℕ} (A : BananaMatrixStructure a 0) :
    BananaCopyRanges A (perfectBanana n) ≃ FixedSubspace a n where
  toFun := fun D => D.leftFixedSubspace
  invFun := A.leftOnlyCopyOfSubspace
  left_inv := by
    intro D
    apply BananaCopyRanges.leftFixedSubspace_injective
    exact A.leftOnlyCopyOfSubspace_range D.leftFixedSubspace
  right_inv := A.leftOnlyCopyOfSubspace_range

/-- Every fixed-dimensional right subspace of a standard perfect
pairing is the image of a copy of any right-only source. -/
theorem BananaMatrixStructure.exists_rightOnlyCopy_overSubspace
    {a n : ℕ} (A : BananaMatrixStructure 0 a)
    (W : FixedSubspace a n) :
    ∃ D : BananaCopyRanges A (perfectBanana n),
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
  let rightMap : (Fin a → F2) →ₗ[F2] (Fin n → F2) :=
    W.1.subtype.comp e.toLinearMap
  have hright : Function.Injective rightMap :=
    W.1.injective_subtype.comp e.injective
  let f : BananaMatrixEmbedding A (perfectBanana n) :=
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
    rw [hx] at hmember
    exact hmember
  · intro hz
    obtain ⟨x, hx⟩ := e.surjective ⟨z, hz⟩
    apply Finset.mem_image.mpr
    refine ⟨x, Finset.mem_univ _, ?_⟩
    change rightMap x = z
    exact congrArg Subtype.val hx

/-- A canonical-for-the-proof unlabelled copy over a right subspace. -/
noncomputable def BananaMatrixStructure.rightOnlyCopyOfSubspace
    {a n : ℕ} (A : BananaMatrixStructure 0 a)
    (W : FixedSubspace a n) :
    BananaCopyRanges A (perfectBanana n) :=
  Classical.choose (A.exists_rightOnlyCopy_overSubspace W)

@[simp] theorem BananaMatrixStructure.rightOnlyCopyOfSubspace_range
    {a n : ℕ} (A : BananaMatrixStructure 0 a)
    (W : FixedSubspace a n) :
    (A.rightOnlyCopyOfSubspace W).rightFixedSubspace = W :=
  Classical.choose_spec (A.exists_rightOnlyCopy_overSubspace W)

/-- The symmetric equivalence between right-only copies and
fixed-dimensional right subspaces in standard perfect pairings. -/
noncomputable def BananaMatrixStructure.rightOnlyCopySubspaceEquiv
    {a n : ℕ} (A : BananaMatrixStructure 0 a) :
    BananaCopyRanges A (perfectBanana n) ≃ FixedSubspace a n where
  toFun := fun D => D.rightFixedSubspace
  invFun := A.rightOnlyCopyOfSubspace
  left_inv := by
    intro D
    apply BananaCopyRanges.rightFixedSubspace_injective
    exact A.rightOnlyCopyOfSubspace_range D.rightFixedSubspace
  right_inv := A.rightOnlyCopyOfSubspace_range

end SuccessorTree.NonPrecompact
