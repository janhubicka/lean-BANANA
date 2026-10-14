import Mathlib.Tactic
import BANANA.NonPrecompact.PrebananaFiniteClass

/-!
# Positive integer margins for refinements of pre-BANANA masses

The reasonability proof for positive S-mass expansions uses a simple
integer fact. For k ≥ 1 children with prescribed parity, give each
an initial positive numerator 1 (odd) or 2 (even). If the prescribed
total N is at least the sum of these minimum numerators and differs
from it by an even integer, one may add the entire even remainder
to one child.

This module formalises that finite bookkeeping step. Selecting a
sufficiently large odd prime power to meet the bound, and the
subsequent positive-mass Fraïssé and EPPA arguments, are separate
proof obligations. The circulation manuscript is unchanged.
-/

namespace SuccessorTree.NonPrecompact

open scoped BigOperators

/-- The least positive numerator of the requested parity. -/
def prebananaMinPositiveNumerator (eps : Bool) : ℕ :=
  if eps then 1 else 2

theorem prebananaMinPositiveNumerator_pos (eps : Bool) :
    0 < prebananaMinPositiveNumerator eps := by
  cases eps <;> decide

theorem prebananaMinPositiveNumerator_mod_two (eps : Bool) :
    prebananaMinPositiveNumerator eps % 2 =
      if eps then 1 else 0 := by
  cases eps <;> decide

/-- Every sufficiently large total with compatible parity splits
into strictly positive numerators with prescribed individual parity.

This is the elementary arithmetic construction used when a positive
mass atom is refined into finitely many children of given markings. -/
theorem prebanana_positive_numerators_of_even_remainder
    {k : ℕ} (hk : 0 < k) (eps : Fin k → Bool) (N : ℕ)
    (hbound :
      (∑ i : Fin k, prebananaMinPositiveNumerator (eps i)) ≤ N)
    (heven :
      Even (N -
        (∑ i : Fin k, prebananaMinPositiveNumerator (eps i)))) :
    ∃ weights : Fin k → ℕ,
      (∀ i, 0 < weights i) ∧
      (∀ i, weights i % 2 = if eps i then 1 else 0) ∧
      (∑ i : Fin k, weights i) = N := by
  classical
  let j : Fin k := ⟨0, hk⟩
  let base : Fin k → ℕ := fun i => prebananaMinPositiveNumerator (eps i)
  let remainder : ℕ := N - ∑ i : Fin k, base i
  let weights : Fin k → ℕ :=
    fun i => base i + if i = j then remainder else 0
  have hrem : remainder % 2 = 0 := by
    obtain ⟨r, hr⟩ := heven
    dsimp [remainder, base] at hr ⊢
    omega
  refine ⟨weights, ?_, ?_, ?_⟩
  · intro i
    have hp := prebananaMinPositiveNumerator_pos (eps i)
    dsimp [weights, base]
    omega
  · intro i
    by_cases hij : i = j
    · subst i
      cases heps : eps j <;>
        simp [weights, base, heps, prebananaMinPositiveNumerator,
          hrem, Nat.add_mod]
    · cases heps : eps i <;>
        simp [weights, base, heps, hij,
          prebananaMinPositiveNumerator]
  · dsimp [weights]
    rw [Finset.sum_add_distrib]
    have hbonus :
        (∑ i : Fin k, (if i = j then remainder else 0)) =
          remainder := by
      simp
    rw [hbonus]
    dsimp [remainder, base] at *
    omega

end SuccessorTree.NonPrecompact
