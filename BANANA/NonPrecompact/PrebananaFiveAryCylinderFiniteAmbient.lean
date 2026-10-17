import BANANA.NonPrecompact.PrebananaFiveAryCylinderFiniteFamily
import BANANA.NonPrecompact.PrebananaFiveAryCylinderMarkedModel
import Mathlib.Order.BooleanSubalgebra

/-!
# Finite Boolean ambient subalgebras for finite cylinder families

Any finite family of elements of the countable pre-BANANA cylinder
algebra sits inside the image of a single finite five-ary stage. That
image is a finite Boolean subalgebra, not merely a finite set.

This lemma is a reusable finite-domain step for extending partial
marked isomorphisms in the later back-and-forth argument. It requires
no ultrahomogeneity or general Fraïssé theorem.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical

/-- Every finite family of cylinder elements is contained in
a finite Boolean subalgebra, realised as an actual finite-stage image. -/
theorem prebananaFiveAryCylinder_finiteAmbient
    {ι : Type*} [Fintype ι]
    (xs : ι → PrebananaFiveAryCylinderLimitCarrier) :
    ∃ S : BooleanSubalgebra PrebananaFiveAryCylinderLimitCarrier,
      Finite S ∧ ∀ i, xs i ∈ S := by
  classical
  obtain ⟨N, ss, hss⟩ :=
    prebananaFiveAryCylinder_finiteFamily_commonStage xs
  let f : BoundedLatticeHom
      (prebananaFiveAryBooleanStage N).carrier
      PrebananaFiveAryCylinderLimitCarrier :=
    prebananaFiveAryCylinderStageHom N
  let S : BooleanSubalgebra PrebananaFiveAryCylinderLimitCarrier :=
    (⊤ : BooleanSubalgebra (prebananaFiveAryBooleanStage N).carrier).map f
  have hsubset :
      (S : Set PrebananaFiveAryCylinderLimitCarrier) ⊆
      Set.range f := by
    intro x hx
    change x ∈
      (⊤ : BooleanSubalgebra (prebananaFiveAryBooleanStage N).carrier).map f
      at hx
    obtain ⟨y, _, hy⟩ := BooleanSubalgebra.mem_map.mp hx
    exact ⟨y, hy⟩
  have hfinite : Finite S :=
    ((Set.finite_range f).subset hsubset).to_subtype
  refine ⟨S, hfinite, ?_⟩
  intro i
  change ∃ y : (prebananaFiveAryBooleanStage N).carrier,
    y ∈ (⊤ : BooleanSubalgebra (prebananaFiveAryBooleanStage N).carrier) ∧
    f y = xs i
  exact ⟨ss i, BooleanSubalgebra.mem_top, hss i⟩

end SuccessorTree.NonPrecompact
