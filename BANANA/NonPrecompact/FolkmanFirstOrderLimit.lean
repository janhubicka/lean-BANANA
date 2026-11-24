import BANANA.NonPrecompact.FolkmanFirstOrderFraisse

/-!
# Finite native diagrams in the encoded Folkman limit

After supplying Fraïssé existence, the encoded limit admits every finite
native paired Boolean-ring structure. Its ultrahomogeneity extends a
native finite diagram using the original, possibly non-unital maps.
-/

namespace SuccessorTree.NonPrecompact

open FirstOrder CategoryTheory
open scoped FirstOrder

variable (M : Bundled.{0} folkmanLanguage.Structure) [Countable M]

/-- Every finite native paired Boolean ring embeds into a first-order
Fraïssé limit of the encoded class. -/
theorem folkmanFirstOrderLimit_nativeEmbeds
    (hM : Language.IsFraisseLimit folkmanFirstOrderClass M)
    {L R : Type} [BooleanRing L] [BooleanRing R] [Fintype L] [Fintype R]
    (P : FolkmanNativeFinitePairing L R) :
    Nonempty (folkmanProductBundle P ↪[folkmanLanguage] M) := by
  have hP := folkmanProductBundle_mem P
  rw [← hM.age] at hP
  exact hP.2

/-- Every finitely generated substructure of the encoded limit is isomorphic
to a native paired Boolean-ring representative. -/
theorem folkmanFirstOrderLimit_substructure_native
    (hM : Language.IsFraisseLimit folkmanFirstOrderClass M)
    (S : folkmanLanguage.Substructure M) (hS : S.FG) :
    ∃ A : FolkmanAtomStructure, Nonempty (S ≃[folkmanLanguage] folkmanFirstOrderRepresentative A) := by
  have hAge := Language.age.fg_substructure hS
  rw [hM.age] at hAge
  exact hAge

/-- Any finite tuple of the encoded limit lies in one embedded native
representative. This allows finite algebraic identities to be checked there. -/
theorem folkmanFirstOrderLimit_tuple_factors
    (hM : Language.IsFraisseLimit folkmanFirstOrderClass M)
    {n : ℕ} (xs : Fin n → M) :
    ∃ (A : FolkmanAtomStructure)
      (f : folkmanFirstOrderRepresentative A ↪[folkmanLanguage] M)
      (ys : Fin n → folkmanFirstOrderRepresentative A),
      ∀ i, f (ys i) = xs i := by
  let S := Language.Substructure.closure folkmanLanguage (Set.range xs)
  let ys : Fin n → S := fun i => ⟨xs i, Language.Substructure.subset_closure ⟨i, rfl⟩⟩
  obtain ⟨A, ⟨e⟩⟩ := folkmanFirstOrderLimit_substructure_native M hM S
    (Language.Substructure.fg_closure (Set.finite_range xs))
  refine ⟨A, S.subtype.comp e.symm.toEmbedding, e ∘ ys, ?_⟩
  intro i
  simp [Function.comp_apply, ys]

/-- An embedding of a finite native source into the encoded limit extends
across every finite native pairing-preserving embedding of that source. -/
theorem folkmanFirstOrderLimit_nativeExtension
    (hM : Language.IsFraisseLimit folkmanFirstOrderClass M)
    {L R L' R' : Type} [BooleanRing L] [BooleanRing R] [Fintype L] [Fintype R]
    [BooleanRing L'] [BooleanRing R'] [Fintype L'] [Fintype R']
    (P : FolkmanNativeFinitePairing L R) (Q : FolkmanNativeFinitePairing L' R')
    (f : folkmanProductBundle P ↪[folkmanLanguage] M)
    (g : FolkmanNativePairingEmbedding P Q) :
    ∃ e : folkmanProductBundle Q ↪[folkmanLanguage] M,
      f = e.comp (show folkmanProductBundle P ↪[folkmanLanguage] folkmanProductBundle Q from
        folkmanNativePairingEmbeddingEquiv P Q g) := by
  have hQ := folkmanFirstOrderLimit_nativeEmbeds M hM Q
  letI : Finite (folkmanProductBundle P) := by
    change Finite (L × R)
    infer_instance
  let hPQ : folkmanProductBundle P ↪[folkmanLanguage] folkmanProductBundle Q :=
    folkmanNativePairingEmbeddingEquiv P Q g
  exact hM.ultrahomogeneous.extend_embedding Language.Structure.FG.of_finite f hPQ (h := hQ)

end SuccessorTree.NonPrecompact
