import BANANA.NonPrecompact.FirstOrderTupleOrbits
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Finite age representatives at each carrier size

An enumeration of a finite age member is a tuple in the ambient structure.
Its automorphism orbit determines the isomorphism type of the finite member.
-/

namespace SuccessorTree.NonPrecompact

open FirstOrder CategoryTheory Set
open scoped FirstOrder

universe w

/-- Finite tuple-orbit quotients give a finite index type of representatives
for each carrier cardinality of the age of a locally finite model. -/
theorem firstOrder_exists_graded_age_representatives
    {L : Language} {M : Type w} [L.Structure M]
    (finiteFG : ∀ S : L.Substructure M, S.FG → Finite S)
    (finiteOrbits : ∀ n : ℕ, Finite (Quotient (firstOrderTupleOrbit L M n))) :
    ∃ (I : ℕ → Type w) (R : ∀ n, I n → Bundled.{w} L.Structure),
      (∀ n, Finite (I n)) ∧
      (∀ n j, R n j ∈ L.age M) ∧
      (∀ n j, Nat.card (R n j) = n) ∧
      ∀ B : Bundled.{w} L.Structure, B ∈ L.age M →
        ∃ j : I (Nat.card B), Nonempty (B ≃[L] R (Nat.card B) j) := by
  classical
  let Q n := Quotient (firstOrderTupleOrbit L M n)
  let S (n : ℕ) (q : Q n) := Language.Substructure.closure L (Set.range q.out)
  let I n := {q : Q n // Nat.card (S n q) = n}
  let R n (j : I n) : Bundled.{w} L.Structure := Bundled.of (S n j.val)
  refine ⟨I, R, ?_, ?_, fun _ j => j.prop, ?_⟩
  · intro n
    let : Finite (Q n) := finiteOrbits n
    exact Finite.of_injective Subtype.val Subtype.val_injective
  · intro n j
    exact Language.age.fg_substructure (Language.Substructure.fg_closure (Set.finite_range j.val.out))
  · intro B hB
    let n := Nat.card B
    obtain ⟨e⟩ := hB.2
    let : Finite e.toHom.range := finiteFG _ (hB.1.range e.toHom)
    let : Finite B := Finite.of_equiv _ e.equivRange.symm.toEquiv
    let : Fintype B := Fintype.ofFinite B
    let list : Fin n ≃ B :=
      (Fintype.equivFinOfCardEq (Nat.card_eq_fintype_card (α := B)).symm).symm
    let tuple : Fin n → M := e ∘ list
    let q : Q n := Quotient.mk (firstOrderTupleOrbit L M n) tuple
    obtain ⟨g, hg⟩ := Quotient.exact (Quotient.out_eq q)
    let f := g.symm.toEmbedding.comp e
    have htuple (idx : Fin n) : f (list idx) = q.out idx := by
      change g.symm (tuple idx) = _
      rw [← hg idx, g.symm_apply_apply]
    have hrange : (f.toHom.range : Set M) = Set.range q.out := by
      change Set.range f = Set.range q.out
      have hfun : f ∘ list = q.out := funext htuple
      rw [← hfun, list.surjective.range_comp]
    have hS : S n q = f.toHom.range := by
      change Language.Substructure.closure L (Set.range q.out) = _
      rw [← hrange, Language.Substructure.closure_eq]
    let equiv : B ≃[L] S n q := hS ▸ f.equivRange
    let j : I n := ⟨q, (Nat.card_congr equiv.toEquiv).symm⟩
    exact ⟨j, ⟨equiv⟩⟩

end SuccessorTree.NonPrecompact
