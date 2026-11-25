import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Equiv.Basic

/-!
# Uniform atom refinement of a finite positive-mass algebra

An atom of mass `a / d` is refined into `a` atoms each of mass `1 / d`.
Partitions of the original atoms with matching masses have blocks of
matching cardinalities in this refinement. A bijection in each block yields
a permutation of the refined atoms.
-/

namespace SuccessorTree.NonPrecompact.BooleanBanana

open scoped BigOperators

private theorem uniform_atom_card_filter {I : Type*} [Fintype I]
    (a : I → ℕ) (P : I → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun x : Σ i, Fin (a i) => P x.1)).card =
      ∑ i ∈ Finset.univ.filter P, a i := by
  classical
  have h : Finset.univ.filter (fun x : Σ i, Fin (a i) => P x.1) =
      (Finset.univ.filter P).sigma (fun i => (Finset.univ : Finset (Fin (a i)))) := by
    ext x
    simp
  rw [h, Finset.card_sigma]
  simp

/-- A positive atom count makes the coordinate projection surjective. -/
theorem uniform_atom_refinement_surjective {I : Type*} (a : I → ℕ)
    (ha : ∀ i, 0 < a i) : Function.Surjective (Sigma.fst : (Σ i, Fin (a i)) → I) :=
  fun i => ⟨⟨i, ⟨0, ha i⟩⟩, rfl⟩

/-- The uniform refinement preserves both the rational mass and the
parity marking of each union of original atoms. -/
theorem uniform_atom_refinement_preserves {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ℕ) (d : ℕ) (s : Finset I) :
    let c := (Finset.univ.filter (fun x : Σ i, Fin (a i) => x.1 ∈ s)).card
    (c : ℚ) / (d : ℚ) = (∑ i ∈ s, (a i : ℚ) / (d : ℚ)) ∧
      (c : ZMod 2) = ∑ i ∈ s, (a i : ZMod 2) := by
  have hs : Finset.univ.filter (fun i => i ∈ s) = s := by ext i; simp
  dsimp only
  rw [uniform_atom_card_filter a (fun i => i ∈ s), hs, Nat.cast_sum, Nat.cast_sum,
    Finset.sum_div]
  exact ⟨rfl, rfl⟩

/-- The same uniform refinement extends every pair of block partitions
whose corresponding blocks have equal rational mass. The common block labels
specify the bijection of blocks, and the permutation intertwines the labels. -/
theorem exists_uniform_atom_permutation {I P : Type*} [Fintype I] [DecidableEq P]
    (a : I → ℕ) {d : ℕ} (hd : d ≠ 0) (s t : I → P)
    (hmass : ∀ j : P,
      (∑ i ∈ Finset.univ.filter (fun i => s i = j), (a i : ℚ) / (d : ℚ)) =
        ∑ i ∈ Finset.univ.filter (fun i => t i = j), (a i : ℚ) / (d : ℚ)) :
    ∃ π : Equiv.Perm (Σ i, Fin (a i)), ∀ x, t (π x).1 = s x.1 := by
  classical
  have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  let refinedS (x : Σ i, Fin (a i)) := s x.1
  let refinedT (x : Σ i, Fin (a i)) := t x.1
  have hcard (j : P) : Fintype.card {x // refinedS x = j} =
      Fintype.card {x // refinedT x = j} := by
    rw [Fintype.card_subtype, Fintype.card_subtype]
    change (Finset.univ.filter (fun x : Σ i, Fin (a i) => s x.1 = j)).card =
      (Finset.univ.filter (fun x : Σ i, Fin (a i) => t x.1 = j)).card
    rw [uniform_atom_card_filter a (fun i => s i = j),
      uniform_atom_card_filter a (fun i => t i = j)]
    have h := hmass j
    simp only [← Finset.sum_div] at h
    have h' := (div_left_inj' hd').mp h
    exact_mod_cast h'
  let byBlock j := Fintype.equivOfCardEq (hcard j)
  exact ⟨Equiv.ofFiberEquiv byBlock, Equiv.ofFiberEquiv_map byBlock⟩

end SuccessorTree.NonPrecompact.BooleanBanana
