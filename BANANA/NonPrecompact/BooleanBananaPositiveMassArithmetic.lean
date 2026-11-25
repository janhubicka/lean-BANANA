import BANANA.NonPrecompact.BooleanBananaPositiveMassMargins
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.ZMod.Basic

/-!
# Positive mass refinements for Boolean–BANANA

Odd common denominators preserve parity. A power of any permitted odd prime
provides enough room for an integer grid or for positive children of prescribed
parities. Dividing by the enlarged denominator preserves the given masses.
-/

namespace SuccessorTree.NonPrecompact.BooleanBanana

open scoped BigOperators

/-- The odd denominators whose prime divisors belong to the allowed set. -/
def positiveMassDenominators (S : Set ℕ) : Submonoid ℕ where
  carrier := {d | Odd d ∧ ∀ q : ℕ, q.Prime → q ∣ d → q ∈ S}
  one_mem' := ⟨odd_one, fun _ hq hdiv => (hq.not_dvd_one hdiv).elim⟩
  mul_mem' ha hb := ⟨ha.1.mul hb.1, fun q hq hdiv =>
    (hq.dvd_mul.mp hdiv).elim (ha.2 q hq) (hb.2 q hq)⟩

private theorem positiveMassDenominator_odd {S : Set ℕ} {d : ℕ}
    (hd : d ∈ positiveMassDenominators S) : Odd d := hd.1

private theorem positiveMassDenominator_pos {S : Set ℕ} {d : ℕ}
    (hd : d ∈ positiveMassDenominators S) : 0 < d := by
  obtain ⟨k, hk⟩ := positiveMassDenominator_odd hd
  omega

private theorem positiveMassDenominator_prime {S : Set ℕ} {p : ℕ}
    (hpS : p ∈ S) (hp : p.Prime) (hpOdd : Odd p) :
    p ∈ positiveMassDenominators S :=
  ⟨hpOdd, fun _ hq hdiv => ((Nat.prime_dvd_prime_iff_eq hq hp).mp hdiv).symm ▸ hpS⟩

private theorem scaled_fraction (a d k : ℕ) (hk : 0 < k) :
    ((a * k : ℕ) : ℚ) / ((d * k : ℕ) : ℚ) = (a : ℚ) / (d : ℚ) := by
  push_cast
  exact mul_div_mul_right _ _ (by exact_mod_cast hk.ne')

private theorem cast_scale_of_odd (a k : ℕ) (hk : Odd k) :
    ((a * k : ℕ) : ZMod 2) = (a : ZMod 2) := by
  rw [Nat.cast_mul, hk.natCast_zmod_two, mul_one]

/-- Reduction modulo two is independent of the chosen odd denominator. -/
theorem positiveMass_odd_fraction_parity {a b d e : ℕ}
    (hd : Odd d) (he : Odd e)
    (h : (a : ℚ) / (d : ℚ) = (b : ℚ) / (e : ℚ)) :
    (a : ZMod 2) = (b : ZMod 2) := by
  have hd0 : (d : ℚ) ≠ 0 := by
    obtain ⟨k, hk⟩ := hd
    exact_mod_cast (show d ≠ 0 by omega)
  have he0 : (e : ℚ) ≠ 0 := by
    obtain ⟨k, hk⟩ := he
    exact_mod_cast (show e ≠ 0 by omega)
  have hmul : a * e = b * d := by
    exact_mod_cast (div_eq_div_iff hd0 he0).mp h
  exact (cast_scale_of_odd a e he).symm.trans
    ((congrArg (fun x : ℕ => (x : ZMod 2)) hmul).trans (cast_scale_of_odd b d hd))

/-- A finite family of positive fractions can be cleared using a single
allowed denominator, while preserving all numerator parities. -/
theorem exists_common_positive_mass_denominator {I : Type*} [Fintype I]
    {S : Set ℕ} (a d : I → ℕ) (ha : ∀ i, 0 < a i)
    (hd : ∀ i, d i ∈ positiveMassDenominators S) :
    ∃ (D : ℕ) (b : I → ℕ), D ∈ positiveMassDenominators S ∧
      ∀ i, 0 < b i ∧ (b i : ℚ) / (D : ℚ) = (a i : ℚ) / (d i : ℚ) ∧
        (b i : ZMod 2) = (a i : ZMod 2) := by
  classical
  let D := ∏ i, d i
  have hD : D ∈ positiveMassDenominators S := Submonoid.prod_mem _ (fun i _ => hd i)
  have hdvd (i : I) : d i ∣ D := Finset.dvd_prod_of_mem d (Finset.mem_univ i)
  choose k hk using hdvd
  refine ⟨D, fun i => a i * k i, hD, fun i => ?_⟩
  have hpos : 0 < k i := by
    apply Nat.pos_of_ne_zero
    intro hz
    have h := positiveMassDenominator_pos hD
    rw [hk i, hz, mul_zero] at h
    exact (Nat.lt_irrefl 0) h
  have hodd : Odd (k i) := by
    apply Nat.Odd.of_mul_right (m := d i)
    rw [← hk i]
    exact positiveMassDenominator_odd hD
  exact ⟨Nat.mul_pos (ha i) hpos, by rw [hk i, scaled_fraction _ _ _ hpos],
    cast_scale_of_odd _ _ hodd⟩

private theorem margin_le_scaled (a n p : ℕ) (ha : 0 < a) (hp : 1 < p) :
    n ≤ a * p ^ n := by
  calc
    n ≤ p ^ n := Nat.le_of_lt (Nat.lt_pow_self hp)
    _ = 1 * p ^ n := (Nat.one_mul _).symm
    _ ≤ a * p ^ n := Nat.mul_le_mul_right _ ha

private theorem scaled_margin_sums {I : Type*} [Fintype I]
    (p d a n : ℕ) (hp : 0 < p) (hpOdd : Odd p) (m : I → ℕ)
    (hm : ∑ i, m i = a * p ^ n) :
    (∑ i, (m i : ℚ) / ((d * p ^ n : ℕ) : ℚ)) = (a : ℚ) / (d : ℚ) ∧
      (∑ i, (m i : ZMod 2)) = (a : ZMod 2) := by
  constructor
  · rw [← Finset.sum_div, ← Nat.cast_sum, hm, scaled_fraction _ _ _ (pow_pos hp _)]
  · rw [← Nat.cast_sum, hm]
    exact cast_scale_of_odd _ _ (hpOdd.pow)

/-- If positive row and column masses have the same total, their integer
grid can be made strictly positive by an allowed odd rescaling. The scaled
grid has the original rational margins and the original parity margins. -/
theorem exists_positive_mass_grid {I J : Type*} [Fintype I] [Fintype J]
    {S : Set ℕ} {p d : ℕ} (hpS : p ∈ S) (hp : p.Prime) (hpOdd : Odd p)
    (hd : d ∈ positiveMassDenominators S)
    (r : I → ℕ) (c : J → ℕ) (hr : ∀ i, 0 < r i) (hc : ∀ j, 0 < c j)
    (h : ∑ i, r i = ∑ j, c j) :
    ∃ (n : ℕ) (m : I → J → ℕ), d * p ^ n ∈ positiveMassDenominators S ∧
      (∀ i j, 0 < m i j) ∧
      (∀ i, (∑ j, (m i j : ℚ) / ((d * p ^ n : ℕ) : ℚ)) = (r i : ℚ) / (d : ℚ) ∧
        (∑ j, (m i j : ZMod 2)) = (r i : ZMod 2)) ∧
      (∀ j, (∑ i, (m i j : ℚ) / ((d * p ^ n : ℕ) : ℚ)) = (c j : ℚ) / (d : ℚ) ∧
        (∑ i, (m i j : ZMod 2)) = (c j : ZMod 2)) := by
  let n := max (Fintype.card I) (Fintype.card J)
  have hr' (i : I) : Fintype.card J ≤ r i * p ^ n :=
    (le_max_right _ _).trans (margin_le_scaled _ _ _ (hr i) hp.one_lt)
  have hc' (j : J) : Fintype.card I ≤ c j * p ^ n :=
    (le_max_left _ _).trans (margin_le_scaled _ _ _ (hc j) hp.one_lt)
  have htotal : (∑ i, r i * p ^ n) = ∑ j, c j * p ^ n := by
    rw [← Finset.sum_mul, ← Finset.sum_mul, h]
  obtain ⟨m, hm, hrow, hcol⟩ :=
    exists_positive_integer_grid (fun i => r i * p ^ n) (fun j => c j * p ^ n)
      hr' hc' htotal
  exact ⟨n, m, (positiveMassDenominators S).mul_mem hd
    (pow_mem (positiveMassDenominator_prime hpS hp hpOdd) n), hm,
    fun i => scaled_margin_sums p d (r i) n hp.pos hpOdd (m i) (hrow i),
    fun j => scaled_margin_sums p d (c j) n hp.pos hpOdd (fun i => m i j) (hcol j)⟩

/-- A parent atom can be split into positive children with the prescribed
parities as soon as their parity sum matches that of the parent. -/
theorem exists_positive_mass_refinement {I : Type*} [Fintype I] [Nonempty I]
    {S : Set ℕ} {p a d : ℕ} (hpS : p ∈ S) (hp : p.Prime) (hpOdd : Odd p)
    (ha : 0 < a) (hd : d ∈ positiveMassDenominators S)
    (mark : I → ZMod 2) (hmark : ∑ i, mark i = (a : ZMod 2)) :
    ∃ (n : ℕ) (m : I → ℕ), d * p ^ n ∈ positiveMassDenominators S ∧
      (∀ i, 0 < m i ∧ (m i : ZMod 2) = mark i) ∧
      (∑ i, (m i : ℚ) / ((d * p ^ n : ℕ) : ℚ)) = (a : ℚ) / (d : ℚ) := by
  classical
  let base (i : I) : ℕ := if mark i = 1 then 1 else 2
  have h01 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  have hbase (i : I) : (base i : ZMod 2) = mark i := by
    have htwo : (2 : ZMod 2) = 0 := by decide
    rcases h01 (mark i) with h | h <;> simp [base, h, htwo]
  let n := ∑ i, base i
  have hn : n ≤ a * p ^ n := margin_le_scaled _ _ _ ha hp.one_lt
  let extra := a * p ^ n - n
  have hextra : (extra : ZMod 2) = 0 := by
    rw [Nat.cast_sub hn, cast_scale_of_odd a _ hpOdd.pow]
    change (a : ZMod 2) - ((∑ i, base i : ℕ) : ZMod 2) = 0
    simp only [Nat.cast_sum, hbase, hmark, sub_self]
  let i₀ : I := Classical.choice ‹Nonempty I›
  let m (i : I) : ℕ := base i + if i = i₀ then extra else 0
  have hm : (∑ i, m i) = a * p ^ n := by
    simp only [m, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact Nat.add_sub_of_le hn
  refine ⟨n, m, (positiveMassDenominators S).mul_mem hd
    (pow_mem (positiveMassDenominator_prime hpS hp hpOdd) n), fun i => ?_,
    (scaled_margin_sums p d a n hp.pos hpOdd m hm).1⟩
  constructor
  · have hi : 0 < base i := by unfold base; split <;> decide
    exact hi.trans_le (Nat.le_add_right _ _)
  · rw [show m i = base i + if i = i₀ then extra else 0 from rfl, Nat.cast_add, hbase]
    split <;> simp [hextra]

end SuccessorTree.NonPrecompact.BooleanBanana
