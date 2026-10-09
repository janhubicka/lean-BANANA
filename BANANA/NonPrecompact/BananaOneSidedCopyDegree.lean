import BANANA.NonPrecompact.BananaOneSidedCopyRanges

/-!
# The one-sided BANANA copy Ramsey theorem in the unlabelled-copy language

The unconditional binary GLR theorem already formalised via
`lean-successors` supplies degree one for colourings of fixed-dimensional
subspaces. The preceding module identifies one-sided BANANA copies with
their nonzero-sort image subspaces, compatibly with embeddings.

We extend a colouring of the realised copy subspaces arbitrarily to
the whole type of fixed-dimensional subspaces. Injectivity of the
representation ensures that restricting this extension recovers the
original colouring exactly. This avoids a choice of bases and also
avoids needing to prove that *every* subspace is realised by a copy
in each arbitrary ambient bilinear system.

No part of the frozen circulation manuscript is changed here.
This file is staged pending a local Lean kernel and axiom audit.
-/

namespace SuccessorTree.NonPrecompact

/-- Extend a finite colouring along an injective map of types by
giving an arbitrary default colour to points outside its range. -/
private noncomputable def extendFiniteColour
    {X Y : Type*} {r : ℕ}
    (f : X → Y)
    (colouring : X → Fin r)
    (fallback : Fin r)
    (y : Y) : Fin r := by
  classical
  exact if h : ∃ x, f x = y then
      colouring (Classical.choose h)
    else fallback

/-- On the image of an injective map the extended colouring
agrees with the original colouring. -/
private theorem extendFiniteColour_apply
    {X Y : Type*} {r : ℕ}
    (f : X → Y)
    (hf : Function.Injective f)
    (colouring : X → Fin r)
    (fallback : Fin r)
    (x : X) :
    extendFiniteColour f colouring fallback (f x) = colouring x := by
  classical
  unfold extendFiniteColour
  split_ifs with h
  · have hchoose : Classical.choose h = x :=
      hf (Classical.choose_spec h)
    rw [hchoose]
  · exact (h ⟨x, rfl⟩).elim

/-- Every left-only finite BANANA source has unlabelled copy
Ramsey degree at most one. This is the fixed-subspace Ramsey
theorem obtained directly from the successor-tree formalisation. -/
theorem BananaMatrixStructure.copyRamseyDegreeLE_one_leftOnly
    {a : ℕ} (A : BananaMatrixStructure a 0) :
    A.copyRamseyDegreeLE 1 := by
  classical
  intro lB rB B colours hcolours
  obtain ⟨n, hRamsey⟩ :=
    (BinaryWord.leftOneSidedCopyRamseyOne_via_successors a)
      lB rB B colours hcolours
  refine ⟨n, n, perfectBanana n, ?_⟩
  intro colouring
  let rangeMap :
      BananaCopyRanges A (perfectBanana n) → FixedSubspace a n :=
    fun D => D.leftFixedSubspace
  have hrange : Function.Injective rangeMap :=
    BananaCopyRanges.leftFixedSubspace_injective
  let fallback : Fin colours := ⟨0, hcolours⟩
  let subspaceColour : FixedSubspace a n → Fin colours :=
    extendFiniteColour rangeMap colouring fallback
  obtain ⟨F, c, hmono⟩ := hRamsey subspaceColour
  refine ⟨F, {c}, by simp, ?_⟩
  intro D
  have hselected :
      subspaceColour ((D.map F).leftFixedSubspace) =
        colouring (D.map F) := by
    exact extendFiniteColour_apply
      rangeMap hrange colouring fallback (D.map F)
  rw [D.leftFixedSubspace_map F] at hselected
  have hcopy : colouring (D.map F) = c :=
    hselected.symm.trans (hmono D.leftFixedSubspace)
  exact Finset.mem_singleton.mpr hcopy

/-- The symmetric degree-one statement for right-only sources. -/
theorem BananaMatrixStructure.copyRamseyDegreeLE_one_rightOnly
    {a : ℕ} (A : BananaMatrixStructure 0 a) :
    A.copyRamseyDegreeLE 1 := by
  classical
  intro lB rB B colours hcolours
  obtain ⟨n, hRamsey⟩ :=
    (BinaryWord.rightOneSidedCopyRamseyOne_via_successors a)
      lB rB B colours hcolours
  refine ⟨n, n, perfectBanana n, ?_⟩
  intro colouring
  let rangeMap :
      BananaCopyRanges A (perfectBanana n) → FixedSubspace a n :=
    fun D => D.rightFixedSubspace
  have hrange : Function.Injective rangeMap :=
    BananaCopyRanges.rightFixedSubspace_injective
  let fallback : Fin colours := ⟨0, hcolours⟩
  let subspaceColour : FixedSubspace a n → Fin colours :=
    extendFiniteColour rangeMap colouring fallback
  obtain ⟨F, c, hmono⟩ := hRamsey subspaceColour
  refine ⟨F, {c}, by simp, ?_⟩
  intro D
  have hselected :
      subspaceColour ((D.map F).rightFixedSubspace) =
        colouring (D.map F) := by
    exact extendFiniteColour_apply
      rangeMap hrange colouring fallback (D.map F)
  rw [D.rightFixedSubspace_map F] at hselected
  have hcopy : colouring (D.map F) = c :=
    hselected.symm.trans (hmono D.rightFixedSubspace)
  exact Finset.mem_singleton.mpr hcopy

/-- The identity embedding, used to witness the existence of at
least one copy of the source inside itself. -/
def BananaMatrixEmbedding.identity
    {l r : ℕ} (A : BananaMatrixStructure l r) :
    BananaMatrixEmbedding A A where
  left := LinearMap.id
  right := LinearMap.id
  left_injective := Function.injective_id
  right_injective := Function.injective_id
  pairing_apply := by
    intro x y
    rfl

/-- Degree zero is impossible for a finite source, since the source
embeds into itself and the set of its own copies is nonempty. -/
theorem BananaMatrixStructure.not_copyRamseyDegreeLE_zero
    {l r : ℕ} (A : BananaMatrixStructure l r) :
    ¬ A.copyRamseyDegreeLE 0 := by
  classical
  intro hdegree
  obtain ⟨lC, rC, C, hC⟩ :=
    hdegree l r A 1 (by decide)
  let colouring : BananaCopyRanges A C → Fin 1 := fun _ => 0
  obtain ⟨f, used, hbound, hcolours⟩ := hC colouring
  have hmem : (0 : Fin 1) ∈ used := by
    have h := hcolours ((BananaMatrixEmbedding.identity A).copyRanges)
    simpa only [colouring] using h
  have hzero : used = ∅ :=
    Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hbound)
  rw [hzero] at hmem
  exact Finset.not_mem_empty _ hmem

/-- The complete copy Ramsey-degree classification, in the same
unlabelled-copy formalisation used for the two-sided obstruction.
The assertions together distinguish degree one from infinity. -/
theorem BananaMatrixStructure.copyRamseyDegree_classification
    {l r : ℕ} (A : BananaMatrixStructure l r) :
    ((r = 0 ∨ l = 0) →
      A.copyRamseyDegreeLE 1 ∧ ¬ A.copyRamseyDegreeLE 0) ∧
    ((0 < l ∧ 0 < r) →
      ∀ t : ℕ, ¬ A.copyRamseyDegreeLE t) := by
  constructor
  · intro h
    rcases h with hr | hl
    · subst r
      exact ⟨A.copyRamseyDegreeLE_one_leftOnly,
        A.not_copyRamseyDegreeLE_zero⟩
    · subst l
      exact ⟨A.copyRamseyDegreeLE_one_rightOnly,
        A.not_copyRamseyDegreeLE_zero⟩
  · rintro ⟨hl, hr⟩
    exact A.copyRamseyDegree_infinite_of_positive hl hr

end SuccessorTree.NonPrecompact
