import BANANA.NonPrecompact.BooleanBananaPositiveMassFinite
import BANANA.NonPrecompact.BooleanBananaMassPrimeRange
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

/-!
# Realising admissible masses using the finite age

A two-atom member of the weighted class has masses n/d and (2d-n)/d.
A mass-preserving embedding of that member into a structure realises
the first fraction on a proper nonzero element, with its prescribed parity.
-/

namespace SuccessorTree.NonPrecompact.BooleanBanana

open scoped BigOperators

variable {B : Type*} [BooleanAlgebra B]

/-- Every positive fraction strictly below two with allowed denominator
is realised in any marked Boolean algebra admitting all the finite
positive-mass models as embeddings. -/
theorem exists_positiveMass_element_of_age {S : Set ℕ} {mark : B → ZMod 2} {mass : B → ℚ}
    (hAge : ∀ (A : Type) [BooleanAlgebra A] [Fintype A]
      (μ : A → ZMod 2) (ρ : A → ℚ), IsFinitePositiveMass S μ ρ →
      ∃ f : BoundedLatticeHom A B, Function.Injective f ∧
        (∀ a, mark (f a) = μ a) ∧ (∀ a, mass (f a) = ρ a))
    {n d : ℕ} (hn : 0 < n) (hnd : n < 2 * d)
    (hd : d ∈ positiveMassDenominators S) :
    ∃ b : B, b ≠ ⊥ ∧ b ≠ ⊤ ∧
      mass b = (n : ℚ) / d ∧ mark b = (n : ZMod 2) := by
  let w₀ : PositiveMassWeight S := ⟨n, d, hn, hd⟩
  let w₁ : PositiveMassWeight S := ⟨2 * d - n, d, Nat.sub_pos_of_lt hnd, hd⟩
  let w : Fin 2 → PositiveMassWeight S := fun i => if i = 0 then w₀ else w₁
  have hdpos : 0 < d := by
    obtain ⟨k, hk⟩ := hd.1
    omega
  have hden : (d : ℚ) ≠ 0 := by exact_mod_cast hdpos.ne'
  have htotal : (∑ i, (w i).mass) = 2 := by
    rw [Fin.sum_univ_two]
    change (w₀.mass + w₁.mass) = 2
    unfold PositiveMassWeight.mass
    change (n : ℚ) / d + ((2 * d - n : ℕ) : ℚ) / d = 2
    rw [← add_div, Nat.cast_sub (Nat.le_of_lt hnd), Nat.cast_mul, Nat.cast_ofNat]
    apply (div_eq_iff hden).2
    ring
  obtain ⟨f, hf, hmark, hmass⟩ := hAge (Finset (Fin 2))
    (fun s => ∑ i ∈ s, (w i).parity) (fun s => ∑ i ∈ s, (w i).mass)
    (weightedPowerset_isFinitePositiveMass w htotal)
  refine ⟨f {0}, ?_, ?_, ?_, ?_⟩
  · intro h
    exact (by decide : ({0} : Finset (Fin 2)) ≠ ⊥) (hf (h.trans (map_bot f).symm))
  · intro h
    exact (by decide : ({0} : Finset (Fin 2)) ≠ ⊤) (hf (h.trans (map_top f).symm))
  · simpa [w, w₀, PositiveMassWeight.mass] using hmass {0}
  · simpa [w, w₀, PositiveMassWeight.parity] using hmark {0}

/-- Every value of the mass map on a union of finite weighted
subalgebras has an allowed denominator and the specified parity. -/
theorem positiveMass_element_fraction_of_finiteCover {S : Set ℕ}
    {mark : B → ZMod 2} {mass : B → ℚ}
    (hcover : ∀ b : B, ∃ (A : Type) (_ : BooleanAlgebra A) (_ : Fintype A)
      (f : BoundedLatticeHom A B) (a : A),
      IsFinitePositiveMass S (mark ∘ f) (mass ∘ f) ∧ f a = b) :
    ∀ b : B, ∃ d n : ℕ, d ∈ positiveMassDenominators S ∧
      (n : ℚ) / (d : ℚ) = mass b ∧ (n : ZMod 2) = mark b := by
  intro b
  obtain ⟨A, hA, hfin, f, a, h, rfl⟩ := hcover b
  letI := hA
  letI := hfin
  exact positiveMass_element_fraction h a

/-- The finite age and finite-subalgebra cover identify the allowed primes
from the normalised mass range of a positive-mass limit. -/
theorem positiveMass_prime_mem_iff_of_age {S : Set ℕ} {mark : B → ZMod 2}
    {mass : B → ℚ}
    (hAge : ∀ (A : Type) [BooleanAlgebra A] [Fintype A]
      (μ : A → ZMod 2) (ρ : A → ℚ), IsFinitePositiveMass S μ ρ →
      ∃ f : BoundedLatticeHom A B, Function.Injective f ∧
        (∀ a, mark (f a) = μ a) ∧ (∀ a, mass (f a) = ρ a))
    (hcover : ∀ b : B, ∃ (A : Type) (_ : BooleanAlgebra A) (_ : Fintype A)
      (f : BoundedLatticeHom A B) (a : A),
      IsFinitePositiveMass S (mark ∘ f) (mass ∘ f) ∧ f a = b)
    {p : ℕ} (hp : p.Prime) (hodd : Odd p) :
    p ∈ S ↔ 1 / (2 * (p : ℝ)) ∈ Set.range (fun b => (mass b : ℝ) / 2) := by
  apply prime_mem_iff_normalizedMass_mem_range _ _ _ hp hodd
  · intro b
    obtain ⟨d, n, hd, hn, _⟩ := positiveMass_element_fraction_of_finiteCover hcover b
    refine ⟨n, d, hd, ?_⟩
    rw [← hn, Rat.cast_div, Rat.cast_natCast, Rat.cast_natCast, div_div, mul_comm]
  · intro q hqS hq hqodd
    have hqden : q ∈ positiveMassDenominators S :=
      ⟨hqodd, fun r hr hrd => ((Nat.prime_dvd_prime_iff_eq hr hq).mp hrd).symm ▸ hqS⟩
    have hqpos := hq.pos
    obtain ⟨b, _, _, hb, _⟩ := exists_positiveMass_element_of_age hAge
      (n := 1) (by decide) (by omega) hqden
    refine ⟨b, ?_⟩
    rw [hb, Rat.cast_div, Rat.cast_natCast, Rat.cast_natCast, div_div, mul_comm]
    norm_num

/-- The finite age realises all masses 2/p^(k+1) on proper nonzero
zero-marked elements; their normalised masses are pairwise distinct. -/
theorem exists_even_marked_mass_sequence_of_age {S : Set ℕ} {mark : B → ZMod 2}
    {mass : B → ℚ}
    (hAge : ∀ (A : Type) [BooleanAlgebra A] [Fintype A]
      (μ : A → ZMod 2) (ρ : A → ℚ), IsFinitePositiveMass S μ ρ →
      ∃ f : BoundedLatticeHom A B, Function.Injective f ∧
        (∀ a, mark (f a) = μ a) ∧ (∀ a, mass (f a) = ρ a))
    {p : ℕ} (hpS : p ∈ S) (hp : p.Prime) (hodd : Odd p) :
    ∃ x : ℕ → B, (∀ k, x k ≠ ⊥ ∧ x k ≠ ⊤ ∧ mark (x k) = 0) ∧
      Function.Injective (fun k => (mass (x k) : ℝ) / 2) := by
  have hden : p ∈ positiveMassDenominators S :=
    ⟨hodd, fun r hr hrd => ((Nat.prime_dvd_prime_iff_eq hr hp).mp hrd).symm ▸ hpS⟩
  have hx (k : ℕ) : ∃ b : B, b ≠ ⊥ ∧ b ≠ ⊤ ∧ mark b = 0 ∧
      (mass b : ℝ) / 2 = 1 / (p : ℝ) ^ (k + 1) := by
    have hpow : 1 < p ^ (k + 1) := one_lt_pow₀ hp.one_lt (Nat.succ_ne_zero k)
    obtain ⟨b, hbot, htop, hb, hm⟩ := exists_positiveMass_element_of_age hAge
      (n := 2) (by decide) (by omega) ((positiveMassDenominators S).pow_mem hden (k + 1))
    refine ⟨b, hbot, htop, hm.trans (by decide), ?_⟩
    rw [hb, Rat.cast_div, Rat.cast_natCast, Rat.cast_natCast, Nat.cast_pow]
    norm_num
    ring
  choose x hx using hx
  refine ⟨x, fun k => ⟨(hx k).1, (hx k).2.1, (hx k).2.2.1⟩, ?_⟩
  intro i j h
  have hh := primePowerMass_injective hp ((hx i).2.2.2.symm.trans (h.trans (hx j).2.2.2))
  omega

end SuccessorTree.NonPrecompact.BooleanBanana
