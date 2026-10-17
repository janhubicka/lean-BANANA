import BANANA.NonPrecompact.PrebananaCountableMarkedBooleanModel
import BANANA.NonPrecompact.PrebananaFiveAryFiniteUniversality
import BANANA.NonPrecompact.PrebananaFiveAryCylinderFiniteEmbeddingFactor
import Mathlib.Order.BooleanSubalgebra

/-!
# The finite age of the countable pre-BANANA cylinder algebra

A finite Boolean subalgebra of the countable cylinder algebra inherits
its admissible F₂ marking and embeds by inclusion. Conversely, every
finite admissibly marked Boolean algebra embeds in the cylinder
algebra, since it embeds into a finite five-ary stage.

The finite subalgebra even factors through a common finite five-ary
stage, by the independent factorisation theorem. These are the age
interfaces required before proving ultrahomogeneity; the assertions
here do not assume an automorphism extension theorem.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical

/-- Compose a finite marked embedding with a finite-to-countable
marked embedding, preserving the complete Boolean operations and
F₂ marking. -/
def PrebananaFiniteToCountableEmbedding.comp
    {A B : PrebananaFiniteBooleanModel}
    {M : PrebananaCountableBooleanModel}
    (g : PrebananaFiniteToCountableEmbedding B M)
    (f : PrebananaFiniteBooleanEmbedding A B) :
    PrebananaFiniteToCountableEmbedding A M where
  hom := g.hom.comp f.hom
  injective := by
    intro x y hxy
    exact f.injective (g.injective hxy)
  preserves_μ := by
    intro x
    exact (g.preserves_μ (f.hom x)).trans (f.preserves_μ x)

/-- Every finite pre-BANANA model embeds into the countable
marked Boolean cylinder model. -/
theorem prebananaCylinder_allFiniteModels_embed
    (B : PrebananaFiniteBooleanModel) :
    Nonempty (PrebananaFiniteToCountableEmbedding
      B prebananaCylinderCountableModel) := by
  obtain ⟨n, ⟨g⟩⟩ := prebananaFiveAry_everyFiniteModel_embeds B
  exact ⟨(prebananaCylinderCountableStageEmbedding n).comp g⟩

/-- Every finite Boolean subalgebra of the cylinder model inherits
the original marking and belongs to the finite pre-BANANA class. -/
noncomputable def prebananaCylinder_finiteSubmodel
    (S : BooleanSubalgebra PrebananaFiveAryCylinderLimitCarrier)
    [Fintype S] : PrebananaFiniteBooleanModel where
  carrier := S
  booleanAlgebra := inferInstance
  finite := inferInstance
  nontrivial := by
    refine ⟨(⊥ : S), (⊤ : S), ?_⟩
    intro h
    have hval : (⊥ : PrebananaFiveAryCylinderLimitCarrier) = ⊤ :=
      congrArg Subtype.val h
    exact (bot_ne_top : (⊥ : PrebananaFiveAryCylinderLimitCarrier) ≠ ⊤) hval
  μ := fun x => prebananaFiveAryCylinderMark x.val
  μ_bot := prebananaFiveAryCylinderMark_bot
  μ_top := prebananaFiveAryCylinderMark_top
  μ_add := by
    intro x y hxy
    change prebananaFiveAryCylinderMark (x.val ⊔ y.val) =
      prebananaFiveAryCylinderMark x.val +
        prebananaFiveAryCylinderMark y.val
    exact prebananaFiveAryCylinderMark_sup x.val y.val
      (congrArg Subtype.val hxy)

/-- A finite subalgebra is a genuine marked substructure, with its
natural marking-preserving inclusion into the countable algebra. -/
noncomputable def prebananaCylinder_finiteSubmodel_embedding
    (S : BooleanSubalgebra PrebananaFiveAryCylinderLimitCarrier)
    [Fintype S] :
    PrebananaFiniteToCountableEmbedding
      (prebananaCylinder_finiteSubmodel S)
      prebananaCylinderCountableModel where
  hom := S.subtype
  injective := Subtype.val_injective
  preserves_μ := by
    intro x
    rfl

/-- A finite Boolean subalgebra of the cylinder limit is contained
in an actual finite five-ary stage as a marked Boolean algebra. -/
theorem prebananaCylinder_finiteSubmodel_factor
    (S : BooleanSubalgebra PrebananaFiveAryCylinderLimitCarrier)
    [Fintype S] :
    ∃ n : ℕ, ∃ g : PrebananaFiniteBooleanEmbedding
        (prebananaCylinder_finiteSubmodel S)
        (prebananaFiveAryBooleanStage n),
      ∀ x : S,
        prebananaFiveAryCylinderStageEmbedding n (g.hom x) = x.val := by
  exact prebananaFiveAryCylinder_finiteEmbedding_factor
    (prebananaCylinder_finiteSubmodel S)
    S.subtype Subtype.val_injective (by intro x; rfl)

end SuccessorTree.NonPrecompact
