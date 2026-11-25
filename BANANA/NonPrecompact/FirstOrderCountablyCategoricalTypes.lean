import Mathlib.ModelTheory.Topology.Types
import Mathlib.ModelTheory.Satisfiability
import BANANA.NonPrecompact.FirstOrderOligomorphicCategoricity

/-!
# Complete types of a countably categorical theory

Downward Löwenheim–Skolem realises every finite type over the empty set
in a countably infinite model. Hence a countably infinite categorical
model realises all such types. Compactness of the type space makes
isolation of all types sufficient for finiteness.
-/

open FirstOrder Cardinal
open scoped FirstOrder

namespace SuccessorTree.NonPrecompact

variable {L : Language.{0, 0}} {M : Type} [L.Structure M]

theorem typeOf_elementaryEmbedding {T : L.Theory} {A B : Type}
    [L.Structure A] [L.Structure B] [Nonempty A] [Nonempty B] [A ⊨ T] [B ⊨ T]
    (f : A ↪ₑ[L] B) {n : ℕ} (v : Fin n → A) :
    T.typeOf (f ∘ v) = T.typeOf v := by
  refine SetLike.ext fun φ => ?_
  simp only [Language.Theory.CompleteType.mem_typeOf]
  exact f.map_formula _ v

/-- Every complete finite type of the theory of an infinite structure in a
countable language is realised in a countably infinite model of that theory. -/
theorem exists_countablyInfinite_model_realizes_completeType [Infinite M]
    (hL : L.card ≤ ℵ₀) {n : ℕ} (p : (L.completeTheory M).CompleteType (Fin n)) :
    ∃ N : (L.completeTheory M).ModelType.{0, 0, 0},
      #N = ℵ₀ ∧ ∃ v : Fin n → N, (L.completeTheory M).typeOf v = p := by
  let T := L.completeTheory M
  obtain ⟨N, v, hv⟩ := T.exists_modelType_is_realized_in p
  have hMN : M ≅[L] N := Language.elementarilyEquivalent_iff.mpr fun φ =>
    (Language.realize_iff_of_model_completeTheory M N φ).symm
  have : Infinite N := hMN.infinite
  have hsmall : #(Set.range v) ≤ ℵ₀ := mk_le_aleph0_iff.mpr inferInstance
  obtain ⟨S, hS, hcard⟩ := L.exists_elementarySubstructure_card_eq
    (Set.range v) (ℵ₀ : Cardinal.{0}) le_rfl (by simp [hsmall]) (by simp [hL])
    (by simp [aleph0_le_mk N])
  let N' := S.toModel T
  let v' : Fin n → N' := fun i => ⟨v i, hS (Set.mem_range_self i)⟩
  refine ⟨N', ?_, v', ?_⟩
  · change #S = ℵ₀
    simpa using hcard
  · exact (typeOf_elementaryEmbedding (T := T) S.subtype v').symm.trans hv

/-- The countably infinite model of a countably categorical theory realises
every complete finite type over the empty set. -/
theorem surjective_typeOf_of_countablyCategorical [Countable M] [Infinite M]
    (hL : L.card ≤ ℵ₀) (hM : (ℵ₀ : Cardinal.{0}).Categorical (L.completeTheory M))
    (n : ℕ) : Function.Surjective
      ((L.completeTheory M).typeOf : (Fin n → M) → (L.completeTheory M).CompleteType (Fin n)) := by
  intro p
  obtain ⟨N, hN, v, hv⟩ := exists_countablyInfinite_model_realizes_completeType hL p
  obtain ⟨f⟩ := hM N (Language.Theory.ModelType.of (L.completeTheory M) M) hN
    (by change #M = ℵ₀; exact Cardinal.mk_eq_aleph0 M)
  refine ⟨f ∘ v, ?_⟩
  exact (typeOf_elementaryEmbedding f.toElementaryEmbedding v).trans hv

/-- If all complete types with a fixed number of free variables are
isolated by a sentence in the language with those variables named,
compactness of the type space makes their number finite. -/
theorem finite_completeType_of_isolated {T : L.Theory} {n : ℕ}
    (h : ∀ p : T.CompleteType (Fin n), ∃ φ : L[[Fin n]].Sentence, T.typesWith φ = {p}) :
    Finite (T.CompleteType (Fin n)) := by
  have : DiscreteTopology (T.CompleteType (Fin n)) :=
    discreteTopology_iff_isOpen_singleton.mpr fun p => by
      obtain ⟨φ, hφ⟩ := h p
      rw [← hφ]
      exact CompleteType.isOpen_typesWith φ
  exact finite_of_compact_of_discrete

end SuccessorTree.NonPrecompact
