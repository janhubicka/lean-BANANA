import BANANA.NonPrecompact.FirstOrderFiniteFraisseExistence
import BANANA.NonPrecompact.FolkmanFirstOrderCategoricity
import BANANA.NonPrecompact.FolkmanFirstOrderFraisse

/-!
# Existence of the countably categorical Folkman–BANANA limit
-/

namespace SuccessorTree.NonPrecompact

open CategoryTheory FirstOrder
open scoped FirstOrder

/-- The encoded finite paired Boolean-ring class has a countable Fraïssé limit. -/
theorem exists_folkmanFirstOrderLimit :
    ∃ (M : Bundled.{0} folkmanLanguage.Structure) (_ : Countable M),
      Language.IsFraisseLimit folkmanFirstOrderClass M := by
  apply exists_finiteFraisseLimit folkmanFirstOrderClass_isFraisse
  rintro M ⟨A, ⟨e⟩⟩
  exact Finite.of_injective e e.injective

/-- There is a countably infinite encoded Folkman–BANANA Fraïssé limit, and
its complete first-order theory is countably categorical. -/
theorem exists_folkmanFirstOrderLimit_categorical :
    ∃ (M : Bundled.{0} folkmanLanguage.Structure) (_ : Countable M),
      Language.IsFraisseLimit folkmanFirstOrderClass M ∧
      Cardinal.mk M = Cardinal.aleph0 ∧
      Cardinal.Categorical Cardinal.aleph0 (folkmanLanguage.completeTheory M) := by
  obtain ⟨M, hM, hFraisse⟩ := exists_folkmanFirstOrderLimit
  exact ⟨M, hM, hFraisse, folkmanFirstOrderLimit_card_aleph0 M hFraisse,
    folkmanFirstOrderLimit_categorical_completeTheory M hFraisse⟩

end SuccessorTree.NonPrecompact
