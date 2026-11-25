import BANANA.NonPrecompact.BooleanBananaPositiveMassEPPA

/-!
# Reasonability and heredity of the finite positive-mass expansion

Every embedding of the marked Boolean reduct lifts if the source has a
positive mass. Restricting a positive mass along a finite Boolean embedding
gives a positive mass on the smaller Boolean algebra.
-/

namespace SuccessorTree.NonPrecompact.BooleanBanana

open scoped BigOperators Classical

/-- Every nonempty Boolean element has positive rational mass. -/
theorem positiveMass_nonzero_pos
    {A : Type*} [BooleanAlgebra A] [Fintype A]
    {S : Set ℕ} {μ : A → ZMod 2} {ρ : A → ℚ}
    (h : IsFinitePositiveMass S μ ρ) {x : A} (hx : x ≠ ⊥) :
    0 < ρ x := by
  classical
  obtain ⟨w, hw, _⟩ := exists_positiveMass_atomCoordinates h
  rw [← hw x]
  apply Finset.sum_pos
  · intro a _
    have hd : 0 < (w a).denominator := by
      obtain ⟨k, hk⟩ := (w a).allowed.1
      omega
    exact div_pos (by exact_mod_cast (w a).positive) (by exact_mod_cast hd)
  · apply Finset.nonempty_iff_ne_empty.mpr
    intro h
    apply hx
    apply (prebananaFiniteBooleanAtomFinsetOrderIso A).injective
    rw [(prebananaFiniteBooleanAtomFinsetOrderIso A).map_bot]
    exact h

/-- Heredity along actual finite Boolean embeddings, including all finite
Boolean subalgebras equipped with the restricted marking and mass. -/
theorem positiveMass_restrict
    {A B : Type*} [BooleanAlgebra A] [Fintype A] [BooleanAlgebra B] [Fintype B]
    {S : Set ℕ} {μ : B → ZMod 2} {ρ : B → ℚ}
    (h : IsFinitePositiveMass S μ ρ)
    (f : BoundedLatticeHom A B) (hf : Function.Injective f) :
    IsFinitePositiveMass S (μ ∘ f) (ρ ∘ f) := by
  constructor
  · simp [h.mass_bot]
  · simp [h.mass_top]
  · intro a b hab
    have hdisj : f a ⊓ f b = ⊥ := by rw [← map_inf, hab, map_bot]
    simpa [map_sup] using h.mass_add _ _ hdisj
  · simp [h.mark_bot]
  · simp [h.mark_top]
  · intro a b hab
    have hdisj : f a ⊓ f b = ⊥ := by rw [← map_inf, hab, map_bot]
    simpa [map_sup] using h.mark_add _ _ hdisj
  · intro a ha
    have hfa : f a ≠ ⊥ := fun hz => ha.ne_bot (hf (hz.trans (map_bot f).symm))
    have hp := positiveMass_nonzero_pos h hfa
    obtain ⟨d, n, hd, hn, hpn⟩ := positiveMass_element_fraction h (f a)
    have hn0 : 0 < n := by
      apply Nat.pos_of_ne_zero
      intro hn0
      rw [hn0, Nat.cast_zero, zero_div] at hn
      exact hp.ne' hn.symm
    exact ⟨⟨n, d, hn0, hd⟩, hn, hpn⟩

set_option maxHeartbeats 500000 in
/-- Lift an arbitrary marking-preserving Boolean embedding from a finite
positive-mass algebra to another admissibly marked finite Boolean algebra. -/
theorem positiveMass_reasonable
    {A B : Type*} [BooleanAlgebra A] [Fintype A] [BooleanAlgebra B] [Fintype B]
    {S : Set ℕ} {p : ℕ} (hpS : p ∈ S) (hp : p.Prime) (hpOdd : Odd p)
    {μA : A → ZMod 2} {ρA : A → ℚ}
    (hA : IsFinitePositiveMass S μA ρA)
    (μB : B → ZMod 2) (hbot : μB ⊥ = 0) (hadd : ∀ x y, x ⊓ y = ⊥ →
      μB (x ⊔ y) = μB x + μB y)
    (f : BoundedLatticeHom A B) (hf : Function.Injective f)
    (hmark : ∀ x, μB (f x) = μA x) :
    ∃ ρB : B → ℚ, IsFinitePositiveMass S μB ρB ∧ ∀ x, ρB (f x) = ρA x := by
  classical
  let eA := prebananaFiniteBooleanAtomFinsetOrderIso A
  let eB := prebananaFiniteBooleanAtomFinsetOrderIso B
  obtain ⟨w, hwρ, hwμ⟩ := exists_positiveMass_atomCoordinates hA
  obtain ⟨part, hsurj, hpart⟩ := exists_positiveMass_atomPartition f hf
  let childMark (b : PrebananaAbstractAtoms B) := μB (eB.symm {b})
  have hchildMark (a : PrebananaAbstractAtoms A) :
      (∑ b : {b // part b = a}, childMark b.1) = (w a).parity := by
    have hsum : (∑ b ∈ Finset.univ.filter (fun b => part b = a), childMark b) =
        ∑ b : {b // part b = a}, childMark b.1 :=
      Finset.sum_subtype (p := fun b => part b = a) _ (fun b => by simp) childMark
    rw [← hsum]
    rw [positiveMass_atomPartition_sum μB childMark
      (fun x => finiteBoolean_additive_sum μB hbot hadd x) f part hpart a, hmark]
    rw [← hwμ (eA.symm {a}), eA.apply_symm_apply, Finset.sum_singleton]
  have hex (a : PrebananaAbstractAtoms A) :
      ∃ k : ℕ, ∃ m : {b // part b = a} → ℕ,
        (w a).denominator * p ^ k ∈ positiveMassDenominators S ∧
        (∀ b, 0 < m b ∧ (m b : ZMod 2) = childMark b.1) ∧
        (∑ b, (m b : ℚ) / (((w a).denominator * p ^ k : ℕ) : ℚ)) = (w a).mass := by
    letI : Nonempty {b // part b = a} :=
      ⟨⟨Classical.choose (hsurj a), Classical.choose_spec (hsurj a)⟩⟩
    exact exists_positive_mass_refinement (I := {b // part b = a})
      (a := (w a).numerator) (d := (w a).denominator) hpS hp hpOdd (w a).positive (w a).allowed
      (fun b => childMark b.1) (hchildMark a)
  choose k m hmden hmpos hmsum using hex
  let wB (b : PrebananaAbstractAtoms B) : PositiveMassWeight S :=
    ⟨m (part b) ⟨b, rfl⟩, (w (part b)).denominator * p ^ k (part b),
      (hmpos _ _).1, hmden _⟩
  have hwBmark (b) : (wB b).parity = childMark b := (hmpos _ _).2
  have hrow (a : PrebananaAbstractAtoms A) :
      (∑ b ∈ Finset.univ.filter (fun b => part b = a), (wB b).mass) = (w a).mass := by
    rw [Finset.sum_subtype (p := fun b => part b = a) _ (fun b => by simp)]
    rw [← hmsum a]
    apply Finset.sum_congr rfl
    rintro ⟨b, hb⟩ _
    subst a
    rfl
  let ρB (x : B) := ∑ b ∈ eB x, (wB b).mass
  have hpres (x : A) : ρB (f x) = ρA x := by
    change (∑ b ∈ eB (f x), (wB b).mass) = _
    rw [hpart x, positiveMassAtomPreimage_sum, ← hwρ x]
    exact Finset.sum_congr rfl (fun a _ => hrow a)
  have htotal : (∑ b, (wB b).mass) = 2 := by
    have h := hpres ⊤
    rw [map_top, hA.mass_top] at h
    change (∑ b ∈ eB ⊤, (wB b).mass) = _ at h
    rw [eB.map_top] at h
    exact h
  have hweight := weightedPowerset_isFinitePositiveMass wB htotal
  have hB := positiveMass_restrict hweight (eB : BoundedLatticeHom B _) eB.injective
  have heq : (fun s : Finset (PrebananaAbstractAtoms B) => ∑ b ∈ s, (wB b).parity) ∘ eB = μB := by
    funext x
    change (∑ b ∈ eB x, (wB b).parity) = μB x
    rw [finiteBoolean_additive_sum μB hbot hadd x]
    exact Finset.sum_congr rfl (fun b _ => hwBmark b)
  exact ⟨ρB, heq ▸ hB, hpres⟩

end SuccessorTree.NonPrecompact.BooleanBanana
