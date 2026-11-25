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

/-- Every countable limit of the encoded Folkman class is infinite because
its age has members with arbitrarily large underlying Boolean rings. -/
theorem folkmanFirstOrderLimit_infinite
    (M : Bundled.{0} folkmanLanguage.Structure) [Countable M]
    (hM : Language.IsFraisseLimit folkmanFirstOrderClass M) :
    Infinite M := by
  classical
  by_contra h
  have : Finite M := not_infinite_iff_finite.mp h
  let : Fintype M := Fintype.ofFinite M
  let n := Fintype.card M
  let A : FolkmanAtomStructure := ⟨n + 1, n + 1, fun _ _ => 0⟩
  have hA := folkmanFirstOrderRepresentative_mem A
  rw [← hM.age] at hA
  obtain ⟨e⟩ := hA.2
  let f : Fin (n + 1) → M := fun i => e (toBoolRing ({i} : Finset (Fin (n + 1))), 0)
  have hf : Function.Injective f := by
    intro i j hij
    have hpair := e.injective hij
    have hfirst : toBoolRing ({i} : Finset (Fin (n + 1))) = toBoolRing {j} :=
      congrArg Prod.fst hpair
    exact Finset.singleton_injective (congrArg ofBoolRing hfirst)
  exact Nat.not_succ_le_self n (by simpa only [Fintype.card_fin] using
      (Fintype.card_le_of_injective f hf))

/-- The encoded limit itself witnesses existence at countably infinite
cardinality for the categorical complete theory. -/
theorem folkmanFirstOrderLimit_card_aleph0
    (M : Bundled.{0} folkmanLanguage.Structure) [Countable M]
    (hM : Language.IsFraisseLimit folkmanFirstOrderClass M) :
    Cardinal.mk M = Cardinal.aleph0 := by
  have := folkmanFirstOrderLimit_infinite M hM
  exact Cardinal.mk_eq_aleph0 M

end SuccessorTree.NonPrecompact
