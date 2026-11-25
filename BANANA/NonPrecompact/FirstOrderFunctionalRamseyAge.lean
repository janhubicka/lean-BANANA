import BANANA.NonPrecompact.FirstOrderNamedClosureExpansion
import BANANA.NonPrecompact.FirstOrderSparseExtensionFamily
import BANANA.NonPrecompact.FirstOrderRamseyExpansion
import BANANA.NonPrecompact.FirstOrderGradedAgeRepresentatives

/-!
# Reasonable precompact Ramsey ages with added functions

The selected-carrier construction produces a genuine Ramsey age on a countable
homogeneous reduct. Here the added language names points of the carrier. The
finite-signature refinement uses a different encoding of the selected family.
-/

namespace SuccessorTree.NonPrecompact

open CategoryTheory FirstOrder
open scoped FirstOrder

universe u v w i

variable {L : Language.{u,v}} {M : Type w} [L.Structure M] [DecidableEq M]

/-- A selected family for a homogeneous strong-amalgamation structure, with
selected embeddings over each member and for every reduct in the age. -/
private theorem exists_selected_family [Countable M] [Infinite M]
    (localFinite : ∀ S : L.Substructure M, S.FG → Finite S)
    (homogeneous : L.IsUltrahomogeneous M)
    (strong : FirstOrderStrongAmalgamation (L.age M))
    {I : ℕ → Type i} (R : ∀ n, I n → Bundled.{w} L.Structure)
    (finiteI : ∀ n, Finite (I n))
    (memR : ∀ n j, R n j ∈ L.age M)
    (cardR : ∀ n j, Nat.card (R n j) = n)
    (covers : ∀ B : Bundled.{w} L.Structure, B ∈ L.age M →
      ∃ j : I (Nat.card B), Nonempty (B ≃[L] R (Nat.card B) j)) :
    ∃ F : FiniteClosureFamily L M,
      (∀ n, {s ∈ F.members | s.card = n}.Finite) ∧
      (∀ B : Bundled.{w} L.Structure, B ∈ L.age M →
        ∃ b : B ↪[L] M, ∃ s ∈ F.members, (s : Set M) = Set.range b) ∧
      (∀ (A B : Bundled.{w} L.Structure), B ∈ L.age M →
        ∀ (e : A ↪[L] B) (a : A ↪[L] M),
          (∃ s ∈ F.members, (s : Set M) = Set.range a) →
          ∃ b : B ↪[L] M, (∀ x, b (e x) = a x) ∧
            ∃ s ∈ F.members, (s : Set M) = Set.range b) := by
  obtain ⟨F, hbase, hclosed, hcofinal, hinter, hsize, hextend⟩ :=
    firstOrder_exists_sparse_extension_family localFinite homogeneous strong
      R finiteI memR cardR covers
  let closureFamily : FiniteClosureFamily L M := {
    members := F
    cofinal := hcofinal
    inter_mem := fun hA hB => hinter _ hA _ hB
    fun_mem := by
      intro S hS n f x hx
      have hx' (j : Fin n) : x j ∈ Language.Substructure.closure L (S : Set M) := by
        change x j ∈ (Language.Substructure.closure L (S : Set M) : Set M)
        rw [hclosed _ hS]
        exact hx j
      have h := (Language.Substructure.closure L (S : Set M)).fun_mem f x hx'
      change Language.Structure.funMap f x ∈ S
      change Language.Structure.funMap f x ∈
        (Language.Substructure.closure L (S : Set M) : Set M) at h
      rwa [hclosed _ hS] at h }
  have hLift := firstOrder_sparse_extension_family_lifts localFinite F hclosed hextend
  refine ⟨closureFamily, hsize, ?_, hLift⟩
  intro B hB
  let e := hB.2.some
  let base := Language.Substructure.closure L (∅ : Set M)
  let A : Bundled.{w} L.Structure := Bundled.of base
  let incl : base ↪[L] e.toHom.range :=
    base.inclusion (Language.Substructure.closure_le.2 (Set.empty_subset _))
  have hb : ∃ s ∈ F, (s : Set M) = Set.range base.subtype := by
    have hrange : Set.range base.subtype = (base : Set M) := by
      ext x
      constructor
      · rintro ⟨a, rfl⟩
        exact a.property
      · intro hx
        exact ⟨⟨x, hx⟩, rfl⟩
    rwa [hrange]
  obtain ⟨b, -, hrange⟩ := hLift A B hB
    (e.equivRange.symm.toEmbedding.comp incl) base.subtype hb
  exact ⟨b, hrange⟩

/-- The actual age of the named expansion is Ramsey, has the prescribed
reduct age, and is reasonable and precompact on the finite reducts. -/
structure IsReasonablePrecompactRamseyAge (F : FiniteClosureFamily L M) : Prop where
  fraisse : Language.IsFraisse (F.expandedLanguage.age M)
  ramsey : FirstOrderEmbeddingRamsey (F.expandedLanguage.age M)
  finite_expansions (A : Bundled.{w} L.Structure) (hA : A ∈ L.age M) :
    (firstOrderCompatibleExpansions F.inclusion (F.expandedLanguage.age M) A).Finite
  reduct_iff (A : Bundled.{w} L.Structure) :
    Nonempty (firstOrderCompatibleExpansions F.inclusion (F.expandedLanguage.age M) A) ↔
      A ∈ L.age M
  reasonable (A B : Bundled.{w} L.Structure) (hB : B ∈ L.age M)
      (a : firstOrderCompatibleExpansions F.inclusion (F.expandedLanguage.age M) A)
      (e : A ↪[L] B) :
    ∃ b : firstOrderCompatibleExpansions F.inclusion (F.expandedLanguage.age M) B,
      ∃ g : @Language.Embedding F.expandedLanguage A B a.val b.val, ∀ x, g x = e x

/-- Strong amalgamation and finite lists of reduct types give a reasonable
precompact Ramsey expansion using added functions and named point predicates. -/
theorem firstOrder_exists_namedFunctionalRamseyAge [Countable M] [Infinite M]
    (localFinite : ∀ S : L.Substructure M, S.FG → Finite S)
    (homogeneous : L.IsUltrahomogeneous M)
    (strong : FirstOrderStrongAmalgamation (L.age M))
    {I : ℕ → Type i} (R : ∀ n, I n → Bundled.{w} L.Structure)
    (finiteI : ∀ n, Finite (I n))
    (memR : ∀ n j, R n j ∈ L.age M)
    (cardR : ∀ n j, Nat.card (R n j) = n)
    (covers : ∀ B : Bundled.{w} L.Structure, B ∈ L.age M →
      ∃ j : I (Nat.card B), Nonempty (B ≃[L] R (Nat.card B) j)) :
    ∃ F : FiniteClosureFamily L M, IsReasonablePrecompactRamseyAge F := by
  obtain ⟨F, hsize, hCoverage, hLift⟩ :=
    exists_selected_family localFinite homogeneous strong R finiteI memR cardR covers
  have finiteAge (A : Bundled.{w} L.Structure) (hA : A ∈ L.age M) : Finite A := by
    let e := hA.2.some
    have := localFinite _ (hA.1.range e.toHom)
    exact Finite.of_injective e.equivRange e.equivRange.injective
  refine ⟨F, F.age_isFraisse, ?_, ?_, ?_, ?_⟩
  · intro A B r _
    obtain ⟨C, hC, h⟩ := F.age_embeddingRamsey A.val B.val B.property r
    exact ⟨⟨C, hC⟩, h⟩
  · intro A hA
    have := finiteAge A hA
    exact (F.finite_labelledStructures hsize).subset fun _ a => a.1.2
  · intro A
    constructor
    · rintro ⟨a⟩
      let : F.expandedLanguage.Structure A := a.val
      let : F.inclusion.IsExpansionOn A := a.property.2
      have : Finite A := F.finite_of_mem_age a.property.1
      exact ⟨Language.Structure.FG.of_finite, ⟨F.reductEmbedding a.property.1.2.some⟩⟩
    · intro hA
      have := finiteAge A hA
      obtain ⟨e, he⟩ := hCoverage A hA
      obtain ⟨S, hS, h⟩ := F.exists_expandedStructure_of_selected_range e he
      exact ⟨⟨S, ⟨Language.Structure.FG.of_finite, h⟩, hS⟩⟩
  · intro A B hB a e
    have := finiteAge B hB
    have : Finite A := Finite.of_injective e e.injective
    let : F.expandedLanguage.Structure A := a.val
    let : F.inclusion.IsExpansionOn A := a.property.2
    obtain ⟨S, hS, b, g, hg, -⟩ := F.exists_expansion_lift
      a.property.1.2.some e (hLift A B hB e)
    exact ⟨⟨S, ⟨Language.Structure.FG.of_finite, ⟨b⟩⟩, hS⟩, g, hg⟩

/-- Oligomorphicity supplies the finite lists of reduct types needed for
the actual precompact Ramsey age construction. -/
theorem firstOrder_exists_namedFunctionalRamseyAge_of_oligomorphic
    {L : Language} {M : Type w} [L.Structure M] [DecidableEq M] [Countable M] [Infinite M]
    (localFinite : ∀ S : L.Substructure M, S.FG → Finite S)
    (homogeneous : L.IsUltrahomogeneous M)
    (strong : FirstOrderStrongAmalgamation (L.age M))
    (finiteOrbits : ∀ n : ℕ, Finite (Quotient (firstOrderTupleOrbit L M n))) :
    ∃ F : FiniteClosureFamily L M, IsReasonablePrecompactRamseyAge F := by
  obtain ⟨I, R, hI, hR, hCard, hCovers⟩ :=
    firstOrder_exists_graded_age_representatives localFinite finiteOrbits
  exact firstOrder_exists_namedFunctionalRamseyAge localFinite homogeneous strong
    R hI hR hCard hCovers

end SuccessorTree.NonPrecompact
