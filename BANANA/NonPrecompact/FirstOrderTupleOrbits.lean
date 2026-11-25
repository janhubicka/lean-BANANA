import BANANA.NonPrecompact.FiniteInvariantRepresentatives
import Mathlib.ModelTheory.Fraisse

/-!
# Finite tuple orbits from finitely many pointed models

An ultrahomogeneous structure has finitely many tuple orbits in a fixed
arity whenever its tuples are images of points in finitely many finitely
generated models. The representatives may depend on the arity.
-/

namespace SuccessorTree.NonPrecompact

open FirstOrder
open scoped FirstOrder

/-- The orbit relation on tuples of a first-order structure under its
actual language automorphisms. -/
def firstOrderTupleOrbit (L : Language) (M : Type*) [L.Structure M] (n : ℕ) :
    Setoid (Fin n → M) where
  r xs ys := ∃ e : M ≃[L] M, ∀ i, e (xs i) = ys i
  iseqv := by
    constructor
    · intro xs
      exact ⟨Language.Equiv.refl _ _, fun _ => rfl⟩
    · rintro xs ys ⟨g, hg⟩
      exact ⟨g.symm, fun i => by rw [← hg i]; exact g.symm_apply_apply _⟩
    · rintro xs ys zs ⟨g, hg⟩ ⟨h, hh⟩
      exact ⟨h.comp g, fun i => by change h (g (xs i)) = zs i; rw [hg, hh]⟩

/-- A finite family of finitely generated models with pointed tuples
covers only finitely many automorphism orbits in an ultrahomogeneous model. -/
theorem finite_firstOrderTupleOrbits_of_pointedCover
    {L : Language} {M : Type*} [L.Structure M] (hM : L.IsUltrahomogeneous M)
    {n : ℕ} {C : Type*} [Finite C] (A : C → Type*) [∀ c, L.Structure (A c)]
    (point : ∀ c, Fin n → A c) (hFG : ∀ c, Language.Structure.FG L (A c))
    (cover : ∀ xs : Fin n → M, ∃ (c : C) (f : A c ↪[L] M), ∀ i, f (point c i) = xs i) :
    Finite (Quotient (firstOrderTupleOrbit L M n)) := by
  classical
  let _ := firstOrderTupleOrbit L M n
  refine finiteQuotient_of_completeFiniteInvariant (fun xs => (cover xs).choose) ?_
  intro xs ys h
  obtain ⟨f, hf⟩ := (cover xs).choose_spec
  obtain ⟨g, hg⟩ := (cover ys).choose_spec
  generalize (cover xs).choose = b at f hf h
  generalize (cover ys).choose = c at g hg h
  subst c
  obtain ⟨e, he⟩ := hM f.toHom.range ((hFG b).range f.toHom)
    (g.comp f.equivRange.symm.toEmbedding)
  refine ⟨e, fun i => ?_⟩
  have hcoord := congrArg (fun j : f.toHom.range ↪[L] M => j (f.equivRange (point b i))) he
  change g (f.equivRange.symm (f.equivRange (point b i))) =
    e (f.equivRange (point b i) : M) at hcoord
  rw [Language.Equiv.symm_apply_apply, Language.Embedding.equivRange_apply, hf i, hg i] at hcoord
  exact hcoord.symm

end SuccessorTree.NonPrecompact
