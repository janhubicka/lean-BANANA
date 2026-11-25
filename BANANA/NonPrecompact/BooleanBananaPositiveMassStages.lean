import BANANA.NonPrecompact.BooleanBananaPositiveMassArithmetic
import Mathlib.Algebra.Group.End
import Mathlib.Logic.Equiv.Prod

/-!
# Uniform positive-mass stages for Boolean–BANANA

A chain of allowed denominators can be chosen cofinally for divisibility,
with each successive quotient greater than one. When every atom has the
same number of children, an atom permutation lifts by retaining the child
labels. These are finite-stage ingredients of the dense-subgroup argument.
-/

namespace SuccessorTree.NonPrecompact.BooleanBanana

/-- A permitted odd prime gives a cofinal increasing denominator chain. -/
theorem exists_positive_mass_denominator_chain {S : Set ℕ} {p : ℕ}
    (hpS : p ∈ S) (hp : p.Prime) (hpOdd : Odd p) :
    ∃ D : ℕ → ℕ, D 0 = 1 ∧ (∀ n, D n ∈ positiveMassDenominators S) ∧
      (∀ n, ∃ k ∈ positiveMassDenominators S, 1 < k ∧ D (n + 1) = D n * k) ∧
      ∀ d ∈ positiveMassDenominators S, ∃ n, d ∣ D n := by
  classical
  let M := positiveMassDenominators S
  have hpM : p ∈ M :=
    ⟨hpOdd, fun _ hq hdiv => ((Nat.prime_dvd_prime_iff_eq hq hp).mp hdiv).symm ▸ hpS⟩
  let factor (n : ℕ) := if n ∈ M then n else 1
  have hfactor (n : ℕ) : factor n ∈ M := by
    unfold factor
    split
    · assumption
    · exact M.one_mem
  let D : ℕ → ℕ := Nat.rec 1 (fun n prev => prev * (p * factor n))
  have hstep (n : ℕ) : D (n + 1) = D n * (p * factor n) := rfl
  have hstepM (n : ℕ) : p * factor n ∈ M := M.mul_mem hpM (hfactor n)
  have hD (n : ℕ) : D n ∈ M := by
    induction n with
    | zero => exact M.one_mem
    | succ n ih =>
      rw [hstep n]
      exact M.mul_mem ih (hstepM n)
  refine ⟨D, rfl, hD, ?_, ?_⟩
  · intro n
    have hpos : 0 < factor n := by
      obtain ⟨j, hj⟩ := (hfactor n).1
      omega
    exact ⟨p * factor n, hstepM n, hp.one_lt.trans_le (Nat.le_mul_of_pos_right _ hpos), hstep n⟩
  · intro d hd
    change d ∈ M at hd
    refine ⟨d + 1, D d * p, ?_⟩
    rw [hstep, show factor d = d by simp [factor, hd]]
    ac_rfl

/-- Lift a permutation to a uniform refinement by keeping each child label. -/
def uniformAtomPermLift (X : Type*) (k : ℕ) :
    Equiv.Perm X →* Equiv.Perm (X × Fin k) where
  toFun π := π.prodCongr (Equiv.refl _)
  map_one' := Equiv.Perm.ext fun _ => rfl
  map_mul' _ _ := Equiv.Perm.ext fun _ => rfl

/-- A nonempty uniform fibre makes the lifting a group embedding. -/
theorem uniformAtomPermLift_injective {X : Type*} {k : ℕ} (hk : 0 < k) :
    Function.Injective (uniformAtomPermLift X k) := by
  intro π τ h
  exact Equiv.Perm.ext fun x => congrArg (fun e : Equiv.Perm (X × Fin k) =>
    (e (x, ⟨0, hk⟩)).1) h

end SuccessorTree.NonPrecompact.BooleanBanana
