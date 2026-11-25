import BANANA.NonPrecompact.BooleanBananaPadicCharge
import BANANA.NonPrecompact.PrebananaBaireOrbit
import Mathlib.Tactic.Ring

/-!
# Meagre orbits on the two-adic charge space

An evaluation at a proper, nonzero Boolean element can be varied by
adding a small even multiple of the difference of two Stone point
masses. Thus its fibres have empty interior. Every orbit has at most
countably many values at such a coordinate if the algebra is countable.
-/

namespace SuccessorTree.NonPrecompact.BooleanBanana

open Set

variable {B : Type*} [BooleanAlgebra B]

private theorem exists_stonePoints (a : B) (ha : a ≠ ⊥) (ht : a ≠ ⊤) :
    ∃ u v : BooleanSpectrum.Space B,
      u ∈ BooleanSpectrum.toSets a ∧ v ∉ BooleanSpectrum.toSets a := by
  have hinj : Function.Injective (BooleanSpectrum.toSets (B := B)) :=
    fun _ _ h => BooleanSpectrum.clopens.injective (SetLike.coe_injective h)
  have hn : (BooleanSpectrum.toSets a).Nonempty := by
    by_contra h
    apply ha (hinj _)
    rw [map_bot]
    exact not_nonempty_iff_eq_empty.mp h
  have hc : (BooleanSpectrum.toSets a)ᶜ.Nonempty := by
    by_contra h
    apply ht (hinj _)
    rw [map_top]
    exact eq_univ_iff_forall.mpr fun v => by
      by_contra hv
      exact h ⟨v, hv⟩
  obtain ⟨u, hu⟩ := hn
  obtain ⟨v, hv⟩ := hc
  exact ⟨u, v, hu, hv⟩

private noncomputable def pointMass (u : BooleanSpectrum.Space B) (a : B) : ℤ_[2] := by
  classical
  exact if u ∈ BooleanSpectrum.toSets a then 1 else 0

private theorem pointMass_add (u : BooleanSpectrum.Space B) (a b : B) (h : Disjoint a b) :
    pointMass u (a ⊔ b) = pointMass u a + pointMass u b := by
  classical
  have hd : Disjoint (BooleanSpectrum.toSets a) (BooleanSpectrum.toSets b) := by
    rw [disjoint_iff, ← map_inf, h.eq_bot, map_bot]
  have hu : u ∈ BooleanSpectrum.toSets (a ⊔ b) ↔
      u ∈ BooleanSpectrum.toSets a ∨ u ∈ BooleanSpectrum.toSets b := by
    rw [map_sup]
    rfl
  by_cases ha : u ∈ BooleanSpectrum.toSets a
  · have hb : u ∉ BooleanSpectrum.toSets b := fun hb => Set.disjoint_left.mp hd ha hb
    simp only [pointMass, hu, ha, hb, true_or, ite_true, ite_false, add_zero]
  · by_cases hb : u ∈ BooleanSpectrum.toSets b <;>
      simp only [pointMass, hu, ha, hb, false_or, ite_true, ite_false, zero_add]

private noncomputable def vary {mark : B → ZMod 2} (c : PadicCharge mark)
    (u v : BooleanSpectrum.Space B) (t : ℤ_[2]) : PadicCharge mark :=
  ⟨fun a => c.val a + 2 * t * (pointMass u a - pointMass v a), by
    classical
    constructor
    · simp [pointMass, c.property.bot]
    · simp [pointMass, c.property.top]
    · intro a b hab
      rw [c.property.add a b hab, pointMass_add u a b hab, pointMass_add v a b hab]
      ring
    · intro a
      rw [map_add, map_mul, map_mul, c.property.parity]
      have htwo : PadicInt.toZMod (2 : ℤ_[2]) = 0 := by
        change PadicInt.toZMod ((2 : ℕ) : ℤ_[2]) = 0
        rw [map_natCast, ZMod.natCast_self]
      rw [htwo, zero_mul, zero_mul, add_zero]⟩

private theorem continuous_vary {mark : B → ZMod 2} (c : PadicCharge mark)
    (u v : BooleanSpectrum.Space B) : Continuous (vary c u v) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro a
  exact continuous_const.add ((continuous_const.mul continuous_id).mul continuous_const)

private theorem exists_ne_zero_of_isOpen (s : Set ℤ_[2]) (hs : IsOpen s) (h : 0 ∈ s) :
    ∃ t ∈ s, t ≠ 0 := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hs 0 h
  obtain ⟨n, hn⟩ := PadicInt.exists_pow_neg_lt 2 hε
  have hnorm : ‖(2 : ℤ_[2]) ^ n‖ = (2 : ℝ) ^ (-(n : ℤ)) := by
    simpa only [Nat.cast_ofNat] using PadicInt.norm_p_pow (p := 2) n
  have htwo : (2 : ℤ_[2]) ≠ 0 := by exact_mod_cast (by decide : (2 : ℕ) ≠ 0)
  refine ⟨(2 : ℤ_[2]) ^ n, hball ?_, pow_ne_zero n htwo⟩
  rw [Metric.mem_ball, dist_eq_norm_sub, sub_zero, hnorm]
  simpa only [Nat.cast_ofNat] using hn

/-- Every fibre of evaluation at a proper, nonzero element has empty interior. -/
theorem interior_padicChargeEvaluation_fibre (mark : B → ZMod 2) {a : B}
    (ha : a ≠ ⊥) (ht : a ≠ ⊤) (r : ℤ_[2]) :
    interior {c : PadicCharge mark | c.val a = r} = ∅ := by
  classical
  apply not_nonempty_iff_eq_empty.mp
  rintro ⟨c, hc⟩
  obtain ⟨u, v, hu, hv⟩ := exists_stonePoints a ha ht
  let fibre : Set (PadicCharge mark) := {d | d.val a = r}
  let s := vary c u v ⁻¹' interior fibre
  have hs : IsOpen s := isOpen_interior.preimage (continuous_vary c u v)
  have hz : (0 : ℤ_[2]) ∈ s := by
    have hvar : vary c u v 0 = c := Subtype.ext (funext fun _ => by simp [vary])
    change vary c u v 0 ∈ interior fibre
    rw [hvar]
    exact hc
  obtain ⟨t, hts, htn⟩ := exists_ne_zero_of_isOpen s hs hz
  have he : vary c u v t ∈ fibre := interior_subset hts
  have hca : c ∈ fibre := interior_subset hc
  change c.val a + 2 * t * (pointMass u a - pointMass v a) = r at he
  change c.val a = r at hca
  have htwo : (2 : ℤ_[2]) ≠ 0 := by exact_mod_cast (by decide : (2 : ℕ) ≠ 0)
  apply mul_ne_zero htwo htn
  have he' : c.val a + 2 * t = c.val a + 0 := by
    simpa only [pointMass, ite_eq_left hu, ite_eq_right hv, sub_zero, mul_one, ← hca,
      add_zero] using he
  exact add_left_cancel he'

/-- On a nonempty charge space over a countable marked Boolean algebra,
the full marking-preserving automorphism group has only meagre orbits,
provided the algebra has a proper, nonzero element. -/
theorem padicChargeOrbit_meagre {mark : B → ZMod 2} [Countable B]
    (c : PadicCharge mark) {a : B} (ha : a ≠ ⊥) (ht : a ≠ ⊤) :
    IsMeagre (MulAction.orbit (markedAutomorphisms mark) c) ∧
      MulAction.orbit (markedAutomorphisms mark) c ∉ residual (PadicCharge mark) := by
  let : Nonempty (PadicCharge mark) := ⟨c⟩
  apply isMeagre_and_not_mem_residual_of_countable_evaluation_range c.val
    (continuous_padicChargeEvaluation mark a)
  · intro d hd
    obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hd
    exact ⟨g.val.symm a, rfl⟩
  · intro r _
    exact interior_padicChargeEvaluation_fibre mark ha ht r

end SuccessorTree.NonPrecompact.BooleanBanana
