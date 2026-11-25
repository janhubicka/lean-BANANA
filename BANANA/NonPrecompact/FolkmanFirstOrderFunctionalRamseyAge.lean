import BANANA.NonPrecompact.FirstOrderFunctionalRamseyAge
import BANANA.NonPrecompact.FolkmanFirstOrderExistence

/-!
# An actual functional Ramsey age over Folkman–BANANA

The reduct uses zero, addition, multiplication and both coordinate
projections as function symbols. Its first-order embeddings are exactly the
native non-unital paired Boolean-ring embeddings.

The chosen expansion uses countably many added function and relation symbols.
The precompactness in this statement counts labelled structures on each
fixed finite reduct in the age.
-/

namespace SuccessorTree.NonPrecompact

open FirstOrder CategoryTheory

private theorem countableFolkmanSymbols : Countable folkmanLanguage.Symbols := by
  have : Countable (Σ n, folkmanLanguage.Relations n) :=
    (show Function.Injective
      (fun x : (Σ n, folkmanLanguage.Relations n) => match x with | ⟨_, .pair a⟩ => a)
      from (by rintro ⟨_, r⟩ ⟨_, s⟩ h; cases r; cases s; cases h; rfl)).countable
  infer_instance

/-- Every countable encoded Folkman–BANANA limit admits a reasonable
precompact Ramsey expansion age in a countable language with added functions. -/
theorem folkmanFirstOrderLimit_exists_namedFunctionalRamseyAge
    (M : Bundled.{0} folkmanLanguage.Structure) [Countable M] [DecidableEq M]
    (hM : Language.IsFraisseLimit folkmanFirstOrderClass M) :
    ∃ F : FiniteClosureFamily folkmanLanguage M,
      Countable F.expandedLanguage.Symbols ∧ IsReasonablePrecompactRamseyAge F := by
  have : Infinite M := folkmanFirstOrderLimit_infinite M hM
  have : Countable folkmanLanguage.Symbols := countableFolkmanSymbols
  have hFinite (S : folkmanLanguage.Substructure M) (hS : S.FG) : Finite S := by
    obtain ⟨_, ⟨e⟩⟩ := folkmanFirstOrderLimit_substructure_native M hM S hS
    exact Finite.of_injective e e.injective
  have hStrong : FirstOrderStrongAmalgamation (folkmanLanguage.age M) := by
    rw [hM.age]
    exact folkmanFirstOrderClass_strongAmalgamation
  obtain ⟨F, hF⟩ := firstOrder_exists_namedFunctionalRamseyAge_of_oligomorphic
    hFinite hM.ultrahomogeneous hStrong (folkmanFirstOrderLimit_tupleOrbits_finite M hM)
  exact ⟨F, inferInstance, hF⟩

/-- An encoded Folkman–BANANA limit and a functional Ramsey expansion
with its actual reduct age. -/
theorem exists_folkmanFirstOrderLimit_namedFunctionalRamseyAge :
    ∃ (M : Bundled.{0} folkmanLanguage.Structure) (_ : Countable M)
      (_ : DecidableEq M) (F : FiniteClosureFamily folkmanLanguage M),
      Language.IsFraisseLimit folkmanFirstOrderClass M ∧
        Countable F.expandedLanguage.Symbols ∧ IsReasonablePrecompactRamseyAge F := by
  classical
  obtain ⟨M, hCount, hM⟩ := exists_folkmanFirstOrderLimit
  let : Countable M := hCount
  obtain ⟨F, hF⟩ := folkmanFirstOrderLimit_exists_namedFunctionalRamseyAge M hM
  exact ⟨M, hCount, Classical.decEq M, F, hM, hF⟩

end SuccessorTree.NonPrecompact
