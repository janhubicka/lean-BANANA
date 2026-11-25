import BANANA.NonPrecompact.BooleanBananaPositiveMassArithmetic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Prime detection from the clopen mass range

The presence of the normalised mass `1/(2p)` detects an allowed odd
prime. Together with the Stone conjugacy theorem, this separates the
subgroups once the positive-mass expansion realises these masses.
-/

namespace SuccessorTree.NonPrecompact.BooleanBanana

/-- Any real fractional representation of `1/(2p)` using an allowed
denominator must use a denominator divisible by `p`. -/
theorem prime_mem_of_normalizedFraction {S : Set ℕ} {p n d : ℕ}
    (hp : p.Prime) (hd : d ∈ positiveMassDenominators S)
    (h : (n : ℝ) / (2 * d) = 1 / (2 * p)) : p ∈ S := by
  have hdpos : 0 < d := by
    obtain ⟨k, hk⟩ := hd.1
    omega
  have hd' : (2 * (d : ℝ)) ≠ 0 := by positivity
  have hp' : (2 * (p : ℝ)) ≠ 0 := by
    exact mul_ne_zero (by norm_num) (by exact_mod_cast hp.ne_zero)
  have hmul := (div_eq_div_iff hd' hp').mp h
  have hx : (n : ℝ) * (p : ℝ) = (d : ℝ) := by linarith
  have hnat : n * p = d := by exact_mod_cast hx
  exact hd.2 p hp ⟨n, hnat.symm.trans (Nat.mul_comm n p)⟩

/-- If a positive-mass range consists of allowed fractions and realises
the unit numerator for every allowed odd prime, it detects those primes. -/
theorem prime_mem_iff_normalizedMass_mem_range {B : Type*} {S : Set ℕ}
    (mass : B → ℝ)
    (hallowed : ∀ b : B, ∃ n d : ℕ, d ∈ positiveMassDenominators S ∧
      mass b = (n : ℝ) / (2 * d))
    (hrealise : ∀ p : ℕ, p ∈ S → p.Prime → Odd p →
      ∃ b : B, mass b = 1 / (2 * p))
    {p : ℕ} (hp : p.Prime) (hodd : Odd p) :
    p ∈ S ↔ (1 / (2 * (p : ℝ))) ∈ Set.range mass := by
  constructor
  · intro hpS
    exact hrealise p hpS hp hodd
  · rintro ⟨b, hb⟩
    obtain ⟨n, d, hd, hmass⟩ := hallowed b
    exact prime_mem_of_normalizedFraction hp hd (hmass.symm.trans hb)

/-- Two mass ranges detecting their sets of permitted odd primes
can coincide only if the permitted sets coincide. -/
theorem positiveMassPrimeSets_eq_of_range_eq {B : Type*} {S T : Set ℕ}
    (m₁ m₂ : B → ℝ)
    (hS : ∀ p ∈ S, p.Prime ∧ Odd p) (hT : ∀ p ∈ T, p.Prime ∧ Odd p)
    (detect₁ : ∀ p, p.Prime → Odd p →
      (p ∈ S ↔ 1 / (2 * (p : ℝ)) ∈ Set.range m₁))
    (detect₂ : ∀ p, p.Prime → Odd p →
      (p ∈ T ↔ 1 / (2 * (p : ℝ)) ∈ Set.range m₂))
    (hrange : Set.range m₁ = Set.range m₂) : S = T := by
  ext p
  constructor
  · intro hp
    obtain ⟨hprime, hodd⟩ := hS p hp
    exact (detect₂ p hprime hodd).mpr (hrange ▸ (detect₁ p hprime hodd).mp hp)
  · intro hp
    obtain ⟨hprime, hodd⟩ := hT p hp
    exact (detect₁ p hprime hodd).mpr (hrange.symm ▸ (detect₂ p hprime hodd).mp hp)

/-- For a fixed odd prime, the normalised masses of elements of total
mass `2/p^k` are pairwise distinct. -/
theorem primePowerMass_injective {p : ℕ} (hp : p.Prime) :
    Function.Injective (fun k : ℕ => 1 / (p : ℝ) ^ k) := by
  have hp' : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  intro k l h
  apply pow_right_injective₀ (lt_trans zero_lt_one hp') hp'.ne'
  exact inv_injective (by simpa only [one_div] using h)

end SuccessorTree.NonPrecompact.BooleanBanana
