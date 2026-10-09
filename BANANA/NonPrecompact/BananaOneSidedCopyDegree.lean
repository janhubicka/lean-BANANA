import BANANA.NonPrecompact.BananaCopySubspaces
import BANANA.NonPrecompact.BananaCopyDegree
import BANANA.NonPrecompact.LinearBinaryRepresentability

/-!
# From binary GLR to unlabelled one-sided BANANA copy degrees

The earlier binary-subspace interface gave monochromatic left/right
subspaces of a target.  Here the passage from subspaces to *copies* is
made explicit: a one-sided copy is uniquely determined by its nonzero
sort's range, and every subspace of the right dimension is such a copy
in a perfect ambient pairing.

The conditional theorems do not assume that the GLR derivation in the
imported successor-tree development has passed its Lean kernel build.
-/

namespace SuccessorTree.NonPrecompact

open Module

/-- Every subspace of the correct dimension is the left range of
a copy of any left-only source inside a standard perfect pairing. -/
theorem BananaMatrixStructure.exists_leftOnlyCopy_with_range
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
  let E : (Fin a → F2) ≃ₗ[F2] W.1 :=
    LinearEquiv.ofFinrankEq (Fin a → F2) W.1 hdim
  let i : (Fin a → F2) →ₗ[F2] (Fin n → F2) :=
    W.1.subtype.comp E.toLinearMap
  have hi : Function.Injective i :=
    W.1.injective_subtype.comp E.injective
  let f : BananaMatrixEmbedding A (perfectBanana n) :=
    { left := i
      right := 0
      left_injective := hi
      right_injective := by
        intro x y _
        exact Subsingleton.elim x y
      pairing_apply := by
        intro x y
        have hy : y = 0 := Subsingleton.elim y 0
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
    have hmem : i x ∈ W.1 := (E x).property
    rw [show i x = z from hx] at hmem
    exact hmem
  · intro hz
    obtain ⟨x, hx⟩ := E.surjective ⟨z, hz⟩
    apply Finset.mem_image.mpr
    refine ⟨x, Finset.mem_univ _, ?_⟩
    change i x = z
    exact congrArg Subtype.val hx

/-- A noncomputable but canonical-for-the-proof representative of
the unique left-only unlabelled copy over a given subspace. -/
noncomputable def BananaMatrixStructure.leftOnlyCopy
    {a n : ℕ} (A : BananaMatrixStructure a 0)
    (W : FixedSubspace a n) :
    BananaCopyRanges A (perfectBanana n) :=
  Classical.choose (A.exists_leftOnlyCopy_with_range W)

@[simp] theorem BananaMatrixStructure.leftOnlyCopy_leftFixedSubspace
    {a n : ℕ} (A : BananaMatrixStructure a 0)
    (W : FixedSubspace a n) :
    (A.leftOnlyCopy W).leftFixedSubspace = W :=
  Classical.choose_spec (A.exists_leftOnlyCopy_with_range W)

/-- Every subspace of the correct dimension is the right range of
a right-only copy inside a standard perfect pairing. -/
theorem BananaMatrixStructure.exists_rightOnlyCopy_with_range
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
  let E : (Fin a → F2) ≃ₗ[F2] W.1 :=
    LinearEquiv.ofFinrankEq (Fin a → F2) W.1 hdim
  let i : (Fin a → F2) →ₗ[F2] (Fin n → F2) :=
    W.1.subtype.comp E.toLinearMap
  have hi : Function.Injective i :=
    W.1.injective_subtype.comp E.injective
  let f : BananaMatrixEmbedding A (perfectBanana n) :=
    { left := 0
      right := i
      left_injective := by
        intro x y _
        exact Subsingleton.elim x y
      right_injective := hi
      pairing_apply := by
        intro x y
        have hx : x = 0 := Subsingleton.elim x 0
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
    have hmem : i x ∈ W.1 := (E x).property
    rw [show i x = z from hx] at hmem
    exact hmem
  · intro hz
    obtain ⟨x, hx⟩ := E.surjective ⟨z, hz⟩
    apply Finset.mem_image.mpr
    refine ⟨x, Finset.mem_univ _, ?_⟩
    change i x = z
    exact congrArg Subtype.val hx

noncomputable def BananaMatrixStructure.rightOnlyCopy
    {a n : ℕ} (A : BananaMatrixStructure 0 a)
    (W : FixedSubspace a n) :
    BananaCopyRanges A (perfectBanana n) :=
  Classical.choose (A.exists_rightOnlyCopy_with_range W)

@[simp] theorem BananaMatrixStructure.rightOnlyCopy_rightFixedSubspace
    {a n : ℕ} (A : BananaMatrixStructure 0 a)
    (W : FixedSubspace a n) :
    (A.rightOnlyCopy W).rightFixedSubspace = W :=
  Classical.choose_spec (A.exists_rightOnlyCopy_with_range W)

/-- An actual one-sided subspace Ramsey statement, not merely a
colouring of embeddings, yields copy Ramsey degree at most one. -/
theorem BananaMatrixStructure.copyRamseyDegreeLE_one_of_leftOneSided
    {a : ℕ} (A : BananaMatrixStructure a 0)
    (hOne : LeftOneSidedCopyRamseyOne a) :
    A.copyRamseyDegreeLE 1 := by
  classical
  intro lB rB B numColours hnum
  obtain ⟨n, hn⟩ := hOne lB rB B numColours hnum
  refine ⟨n, n, perfectBanana n, ?_⟩
  intro colouring
  let subspaceColour : FixedSubspace a n → Fin numColours :=
    fun W => colouring (A.leftOnlyCopy W)
  obtain ⟨F, c, hc⟩ := hn subspaceColour
  refine ⟨F, {c}, by simp, ?_⟩
  intro D
  have hcopy :
      A.leftOnlyCopy
        (D.leftFixedSubspace.map F.left F.left_injective) =
          D.map F := by
    apply BananaCopyRanges.ext_of_leftFixedSubspace_eq
    rw [A.leftOnlyCopy_leftFixedSubspace,
      D.leftFixedSubspace_map]
  rw [← hcopy, Finset.mem_singleton]
  simpa only [subspaceColour] using hc D.leftFixedSubspace

/-- The symmetric unlabelled right-copy degree-one implication. -/
theorem BananaMatrixStructure.copyRamseyDegreeLE_one_of_rightOneSided
    {a : ℕ} (A : BananaMatrixStructure 0 a)
    (hOne : RightOneSidedCopyRamseyOne a) :
    A.copyRamseyDegreeLE 1 := by
  classical
  intro lB rB B numColours hnum
  obtain ⟨n, hn⟩ := hOne lB rB B numColours hnum
  refine ⟨n, n, perfectBanana n, ?_⟩
  intro colouring
  let subspaceColour : FixedSubspace a n → Fin numColours :=
    fun W => colouring (A.rightOnlyCopy W)
  obtain ⟨F, c, hc⟩ := hn subspaceColour
  refine ⟨F, {c}, by simp, ?_⟩
  intro D
  have hcopy :
      A.rightOnlyCopy
        (D.rightFixedSubspace.map F.right F.right_injective) =
          D.map F := by
    apply BananaCopyRanges.ext_of_rightFixedSubspace_eq
    rw [A.rightOnlyCopy_rightFixedSubspace,
      D.rightFixedSubspace_map]
  rw [← hcopy, Finset.mem_singleton]
  simpa only [subspaceColour] using hc D.rightFixedSubspace

/-- The source-level one-sided copy statements, conditional on the
concrete successor-tree representation proof compiling successfully. -/
theorem BananaMatrixStructure.copyRamseyDegreeLE_one_left_via_successors
    {a : ℕ} (A : BananaMatrixStructure a 0) :
    A.copyRamseyDegreeLE 1 :=
  A.copyRamseyDegreeLE_one_of_leftOneSided
    (BinaryWord.leftOneSidedCopyRamseyOne_via_successors a)

theorem BananaMatrixStructure.copyRamseyDegreeLE_one_right_via_successors
    {a : ℕ} (A : BananaMatrixStructure 0 a) :
    A.copyRamseyDegreeLE 1 :=
  A.copyRamseyDegreeLE_one_of_rightOneSided
    (BinaryWord.rightOneSidedCopyRamseyOne_via_successors a)

/-- The identity embedding witnesses that an unlabelled A-copy always
exists in A itself.  This is independent of any Ramsey theorem. -/
def BananaMatrixStructure.identityCopyEmbedding
    {l r : ℕ} (A : BananaMatrixStructure l r) :
    BananaMatrixEmbedding A A where
  left := LinearMap.id
  right := LinearMap.id
  left_injective := fun _ _ h => h
  right_injective := fun _ _ h => h
  pairing_apply := by
    intro x y
    rfl

/-- The copy Ramsey degree of any finite BANANA source cannot be zero.
Taking the target equal to the source forces a copy to occur. -/
theorem BananaMatrixStructure.not_copyRamseyDegreeLE_zero
    {l r : ℕ} (A : BananaMatrixStructure l r) :
    ¬ A.copyRamseyDegreeLE 0 := by
  classical
  intro hzero
  obtain ⟨lC, rC, C, hC⟩ :=
    hzero l r A 1 (by omega)
  let colouring : BananaCopyRanges A C → Fin 1 := fun _ => 0
  obtain ⟨f, used, husedCard, hused⟩ := hC colouring
  have hmem : (0 : Fin 1) ∈ used :=
    hused (A.identityCopyEmbedding.copyRanges)
  have hpos : 0 < used.card :=
    Finset.card_pos.mpr ⟨0, hmem⟩
  omega

/-- Both one-sided classes have degree exactly one in the sense of the
two separate bounds; the zero-dimensional source is included. -/
theorem BananaMatrixStructure.leftOnly_copy_degree_exactly_one
    {a : ℕ} (A : BananaMatrixStructure a 0) :
    A.copyRamseyDegreeLE 1 ∧ ¬ A.copyRamseyDegreeLE 0 :=
  ⟨A.copyRamseyDegreeLE_one_left_via_successors,
    A.not_copyRamseyDegreeLE_zero⟩

theorem BananaMatrixStructure.rightOnly_copy_degree_exactly_one
    {a : ℕ} (A : BananaMatrixStructure 0 a) :
    A.copyRamseyDegreeLE 1 ∧ ¬ A.copyRamseyDegreeLE 0 :=
  ⟨A.copyRamseyDegreeLE_one_right_via_successors,
    A.not_copyRamseyDegreeLE_zero⟩

end SuccessorTree.NonPrecompact
