import BANANA.NonPrecompact.FolkmanAtomCode
import BANANA.NonPrecompact.FolkmanFirstOrderLanguage
import Mathlib.ModelTheory.Fraisse

/-!
# The first-order class of finite Folkman atom codes

These bundled representatives and local diagram lemmas can be used with
the mathlib Fraïssé limit interface independently of the proof of
amalgamation and existence of the finite class.
-/

namespace SuccessorTree.NonPrecompact

open FirstOrder CategoryTheory
open scoped FirstOrder

/-- Bundle a native paired ring product for the mathlib Fraïssé API. -/
def folkmanProductBundle {L R : Type} [BooleanRing L] [BooleanRing R]
    (P : FolkmanNativeFinitePairing L R) : Bundled.{0} folkmanLanguage.Structure :=
  ⟨L × R, folkmanProductStructure P.pairing⟩

/-- The first-order structure attached to a finite atom code. -/
noncomputable def folkmanFirstOrderRepresentative (A : FolkmanAtomStructure) :
    Bundled.{0} folkmanLanguage.Structure :=
  folkmanProductBundle (folkmanNativeCodeRealisation A)

instance (A : FolkmanAtomStructure) : Finite (folkmanFirstOrderRepresentative A) := by
  change Finite (FolkmanNativeCodeRing A.leftCount × FolkmanNativeCodeRing A.rightCount)
  infer_instance

/-- The isomorphism closure of the finite Folkman atom representatives. -/
def folkmanFirstOrderClass : Set (Bundled.{0} folkmanLanguage.Structure) :=
  {M | ∃ A : FolkmanAtomStructure, Nonempty (M ≃[folkmanLanguage] folkmanFirstOrderRepresentative A)}

theorem folkmanFirstOrderRepresentative_mem (A : FolkmanAtomStructure) :
    folkmanFirstOrderRepresentative A ∈ folkmanFirstOrderClass :=
  ⟨A, ⟨Language.Equiv.refl _ _⟩⟩

variable (M : Bundled.{0} folkmanLanguage.Structure) [Countable M]

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

end SuccessorTree.NonPrecompact
