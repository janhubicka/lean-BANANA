import BANANA.NonPrecompact.BananaLimitDefinableColouring
import BANANA.NonPrecompact.FirstOrderInvariantTypes

/-!
# Invariant types for the tagged BANANA theory

The definable tuple Ramsey theorem and isolation of finite tuple types
give an invariant global extension of every complete type over the
empty set, including the type of the model's enumeration. This is first-order extreme amenability in the
invariant-type formulation.
-/

namespace SuccessorTree.NonPrecompact

open FirstOrder
open scoped FirstOrder

private theorem bananaTagged_model_finiteTupleTypes_isolated
    (M : Type*) [bananaTaggedLanguage.Structure M]
    [M ⊨ bananaTaggedLanguage.completeTheory BananaTaggedCarrier]
    (n : ℕ) (b : Fin n → M) :
    ∃ θ : bananaTaggedLanguage.Formula (Fin n),
      ∀ z : Fin n → M, θ.Realize z ↔ SameFormulaType (L := bananaTaggedLanguage) b z := by
  have hM : BananaTaggedCarrier ≅[bananaTaggedLanguage] M :=
    Language.elementarilyEquivalent_iff.mpr fun φ =>
      (Language.realize_iff_of_model_completeTheory BananaTaggedCarrier M φ).symm
  obtain ⟨R, hR⟩ := bananaLimit_firstOrder_finite_tuple_orbit_representatives n
  have hCover := formula_type_cover_of_finset_automorphism_orbit_representatives R hR
  obtain ⟨i, hi⟩ := finite_formula_type_cover_of_elementarilyEquivalent hM
    (fun s : R => s.val) hCover b
  obtain ⟨θ, hθ⟩ := exists_formula_isolates_in_finite_type_cover
    (fun s : R => s.val) hCover i.val
  refine ⟨θ, fun z => (isolates_formula_type_of_elementarilyEquivalent hM hθ z).trans ?_⟩
  exact ⟨fun h => hi.symm.trans h, fun h => hi.trans h⟩

/-- Every type over the empty set in the complete tagged BANANA theory
has an invariant complete extension over each model of the theory. -/
theorem bananaTagged_completeTheory_exists_invariantExtension
    (M : Type*) [bananaTaggedLanguage.Structure M] [Nonempty M]
    [M ⊨ bananaTaggedLanguage.completeTheory BananaTaggedCarrier]
    {α : Type*} (p₀ : (bananaTaggedLanguage.completeTheory BananaTaggedCarrier).CompleteType α) :
    ∃ p : (bananaTaggedLanguage.elementaryDiagram M).CompleteType α, IsInvariantType p ∧
      ∀ (φ : bananaTaggedLanguage.Formula α), Language.Formula.equivSentence φ ∈ p₀ →
        Language.Formula.equivSentence ((bananaTaggedLanguage.lhomWithConstants M).onFormula φ) ∈ p := by
  have hM : BananaTaggedCarrier ≅[bananaTaggedLanguage] M :=
    Language.elementarilyEquivalent_iff.mpr fun φ =>
      (Language.realize_iff_of_model_completeTheory BananaTaggedCarrier M φ).symm
  revert p₀
  rw [hM.completeTheory_eq]
  exact HasDefinableTupleRamsey.exists_invariantExtension
    (bananaTagged_completeTheory_hasDefinableTupleRamsey M)
    (bananaTagged_model_finiteTupleTypes_isolated M)

/-- Every model of the complete tagged BANANA theory admits an invariant
complete type of its own enumeration over that model. In particular,
the theorem applies to a monster model to give first-order extreme
amenability of the tagged theory. -/
theorem bananaTagged_completeTheory_exists_invariantEnumerationType
    (M : Type*) [bananaTaggedLanguage.Structure M] [Nonempty M]
    [M ⊨ bananaTaggedLanguage.completeTheory BananaTaggedCarrier] :
    ∃ p : (bananaTaggedLanguage.elementaryDiagram M).CompleteType M, IsInvariantType p ∧
      ∀ (φ : bananaTaggedLanguage.Formula M), φ.Realize (id : M → M) →
        Language.Formula.equivSentence ((bananaTaggedLanguage.lhomWithConstants M).onFormula φ) ∈ p := by
  exact HasDefinableTupleRamsey.exists_invariantType
    (bananaTagged_completeTheory_hasDefinableTupleRamsey M)
    (bananaTagged_model_finiteTupleTypes_isolated M) id

end SuccessorTree.NonPrecompact
