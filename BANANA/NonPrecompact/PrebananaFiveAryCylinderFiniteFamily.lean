import BANANA.NonPrecompact.PrebananaFiveAryCylinderMark

/-!
# A common finite stage for every finite family of cylinders

Each element of the countable pre-BANANA cylinder algebra has a
presentation as a subset of finite five-ary words. A *finite family*
of such elements can be presented simultaneously at one finite stage:
choose one depth per member and refine all of them to the maximum.

This lemma is the common-stage factorisation needed to transfer
finite Boolean subalgebras and their markings to the actual finite
five-ary stages. It does not yet assert a Fraïssé limit or the
extension of finite partial isomorphisms.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical

/-- Every finite family of cylinders comes from one actual stage of
the explicit five-ary tower, simultaneously for every family member. -/
theorem prebananaFiveAryCylinder_finiteFamily_commonStage
    {ι : Type*} [Fintype ι]
    (X : ι → PrebananaFiveAryCylinderLimitCarrier) :
    ∃ n : ℕ, ∃ s : ι → Finset (PrebananaFiveAryWord n),
      ∀ i, prebananaFiveAryCylinderStageEmbedding n (s i) = X i := by
  classical
  let depth (i : ι) : ℕ := Classical.choose (X i).property
  let words (i : ι) : Finset (PrebananaFiveAryWord (depth i)) :=
    Classical.choose (Classical.choose_spec (X i).property)
  have hrepr (i : ι) :
      (X i).val = prebananaFiveAryCylinder (depth i) (words i) := by
    exact Classical.choose_spec (Classical.choose_spec (X i).property)
  let N := Finset.univ.sup depth
  have hdepth (i : ι) : depth i ≤ N := by
    exact Finset.le_sup (Finset.mem_univ i)
  let lifts (i : ι) : Finset (PrebananaFiveAryWord N) :=
    prebananaFiveAryRefineTo (depth i) N (hdepth i) (words i)
  refine ⟨N, lifts, ?_⟩
  intro i
  apply Subtype.ext
  change prebananaFiveAryCylinder N (lifts i) = (X i).val
  calc
    prebananaFiveAryCylinder N (lifts i) =
      prebananaFiveAryCylinder (depth i) (words i) :=
        prebananaFiveAryRefineTo_cylinder
          (depth i) N (hdepth i) (words i)
    _ = (X i).val := (hrepr i).symm

/-- The simultaneous finite-stage presentation preserves the
stage-independent F₂ marking of every member of a finite family. -/
theorem prebananaFiveAryCylinder_finiteFamily_commonStage_mark
    {ι : Type*} [Fintype ι]
    (X : ι → PrebananaFiveAryCylinderLimitCarrier) :
    ∃ n : ℕ, ∃ s : ι → Finset (PrebananaFiveAryWord n),
      (∀ i, prebananaFiveAryCylinderStageEmbedding n (s i) = X i) ∧
      ∀ i, (prebananaFiveAryBooleanStage n).μ (s i) =
        prebananaFiveAryCylinderMark (X i) := by
  obtain ⟨n, s, h⟩ :=
    prebananaFiveAryCylinder_finiteFamily_commonStage X
  refine ⟨n, s, h, ?_⟩
  intro i
  rw [← h i]
  exact (prebananaFiveAryCylinderStageEmbedding_mark n (s i)).symm

end SuccessorTree.NonPrecompact
