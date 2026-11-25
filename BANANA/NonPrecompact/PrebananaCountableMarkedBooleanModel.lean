import BANANA.NonPrecompact.PrebananaMarkedBooleanModels
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
