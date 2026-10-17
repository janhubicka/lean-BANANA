import BANANA.NonPrecompact.PrebananaFiveAryCylinderMarkedModel

/-!
# Countable marked Boolean algebras and finite-to-countable embeddings

The finite pre-BANANA class has a marking µ : B → F₂ which vanishes
at bottom and top and is additive on disjoint joins. The same
language and axioms make sense on a countable Boolean algebra.

This file packages the explicit cylinder construction as a genuine
countable marked Boolean algebra, and its finite-stage inclusions
as marking-preserving embeddings in the complete Boolean language.

Universality and ultrahomogeneity are *not* included in the
definition; they are separate mathematical obligations.
-/

namespace SuccessorTree.NonPrecompact

/-- A countable, nontrivial Boolean algebra with an admissible
disjoint-additive F₂ marking. -/
structure PrebananaCountableBooleanModel where
  carrier : Type
  [booleanAlgebra : BooleanAlgebra carrier]
  [countable : Countable carrier]
  [nontrivial : Nontrivial carrier]
  μ : carrier → F2
  μ_bot : μ ⊥ = 0
  μ_top : μ ⊤ = 0
  μ_add : ∀ x y : carrier, x ⊓ y = ⊥ →
    μ (x ⊔ y) = μ x + μ y

attribute [instance] PrebananaCountableBooleanModel.booleanAlgebra
  PrebananaCountableBooleanModel.countable
  PrebananaCountableBooleanModel.nontrivial

/-- An actual marked embedding from an arbitrary finite
pre-BANANA algebra into a countable marked Boolean algebra. -/
structure PrebananaFiniteToCountableEmbedding
    (A : PrebananaFiniteBooleanModel)
    (M : PrebananaCountableBooleanModel) where
  hom : BoundedLatticeHom A.carrier M.carrier
  injective : Function.Injective hom
  preserves_μ : ∀ x : A.carrier, M.μ (hom x) = A.μ x

/-- The countable cylinder algebra with its stage-independent
F₂ marking is an actual countable pre-BANANA structure. -/
noncomputable def prebananaCylinderCountableModel :
    PrebananaCountableBooleanModel where
  carrier := PrebananaFiveAryCylinderLimitCarrier
  μ := prebananaFiveAryCylinderMark
  μ_bot := prebananaFiveAryCylinderMark_bot
  μ_top := prebananaFiveAryCylinderMark_top
  μ_add := prebananaFiveAryCylinderMark_sup

/-- Every finite five-ary word stage embeds as a genuine
marked Boolean substructure of the countable cylinder model. -/
noncomputable def prebananaCylinderCountableStageEmbedding (n : ℕ) :
    PrebananaFiniteToCountableEmbedding
      (prebananaFiveAryBooleanStage n)
      prebananaCylinderCountableModel where
  hom := prebananaFiveAryCylinderStageHom n
  injective := prebananaFiveAryCylinderStageHom_injective n
  preserves_μ := prebananaFiveAryCylinderStageHom_preserves_mark n

end SuccessorTree.NonPrecompact
