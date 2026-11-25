import BANANA.NonPrecompact.BooleanBananaPadicCharge

/-!
# Residue approximations in the two-adic charge flow

Finite-coordinate residue approximations imply density of the actual
automorphism orbit in the product subspace topology.
-/

namespace SuccessorTree.NonPrecompact.BooleanBanana

open Set

variable {B : Type*} [BooleanAlgebra B]

private theorem exists_padicResidue_fibre_subset
    (x : ℤ_[2]) {U : Set ℤ_[2]} (hU : IsOpen U) (hx : x ∈ U) :
    ∃ n : ℕ, ∀ y : ℤ_[2], PadicInt.toZModPow n y = PadicInt.toZModPow n x → y ∈ U := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU x hx
  obtain ⟨n, hn⟩ := PadicInt.exists_pow_neg_lt (p := 2) hε
  refine ⟨n, fun y hy => hball ?_⟩
  apply Metric.mem_ball.mpr
  apply lt_of_le_of_lt _ hn
  rw [dist_eq_norm, PadicInt.norm_le_pow_iff_mem_span_pow,
    ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, hy, sub_self]

/-- A single group element approximating finitely many coordinates
modulo any power of two gives a dense orbit in the charge space. -/
theorem dense_padicChargeOrbit_of_finiteResidues
    {mark : B → ZMod 2} (c : PadicCharge mark)
    (hres : ∀ (d : PadicCharge mark) (F : Finset B) (n : ℕ),
      ∃ g : markedAutomorphisms mark, ∀ b ∈ F,
        PadicInt.toZModPow n ((g • c).val b) = PadicInt.toZModPow n (d.val b)) :
    Dense (MulAction.orbit (markedAutomorphisms mark) c) := by
  classical
  rw [dense_iff_inter_open]
  intro U hU hUne
  obtain ⟨V, hV, rfl⟩ := isOpen_induced_iff.mp hU
  obtain ⟨d, hd⟩ := hUne
  obtain ⟨F, W, hW, hsubset⟩ := isOpen_pi_iff.mp hV d.val hd
  have fibres (b : B) (hb : b ∈ F) :=
    exists_padicResidue_fibre_subset (d.val b) (hW b hb).1 (hW b hb).2
  choose exponent hexp using fibres
  let k (b : B) := if hb : b ∈ F then exponent b hb else 0
  let n := F.sup k
  obtain ⟨g, hg⟩ := hres d F n
  refine ⟨g • c, hsubset ?_, ⟨g, rfl⟩⟩
  intro b hb
  have hkn : k b ≤ n := Finset.le_sup (f := k) hb
  rw [show k b = exponent b hb from dite_eq_left hb] at hkn
  apply hexp b hb _
  rw [← PadicInt.cast_toZModPow (exponent b hb) n hkn,
    ← PadicInt.cast_toZModPow (exponent b hb) n hkn, hg b hb]

end SuccessorTree.NonPrecompact.BooleanBanana
