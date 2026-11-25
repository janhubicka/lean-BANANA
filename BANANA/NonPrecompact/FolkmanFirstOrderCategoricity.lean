import BANANA.NonPrecompact.FolkmanFirstOrderOrbits
import BANANA.NonPrecompact.FirstOrderOligomorphicCategoricity

/-!
# Countable categoricity of the encoded Folkman–BANANA limit

The finite tuple-orbit quotient of the encoded limit yields categoricity
of its complete theory by the first-order finite type cover argument.
-/

namespace SuccessorTree.NonPrecompact

open CategoryTheory FirstOrder
open scoped FirstOrder

/-- The complete theory of any encoded countable Folkman–BANANA
Fraïssé limit is `ℵ₀`-categorical. -/
theorem folkmanFirstOrderLimit_categorical_completeTheory
    (M : Bundled.{0} folkmanLanguage.Structure) [Countable M]
    (hM : Language.IsFraisseLimit folkmanFirstOrderClass M) :
    Cardinal.Categorical Cardinal.aleph0 (folkmanLanguage.completeTheory M) :=
  categorical_completeTheory_of_finite_tupleOrbitQuotients
    (folkmanFirstOrderLimit_tupleOrbits_finite M hM)

end SuccessorTree.NonPrecompact
