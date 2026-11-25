import BANANA.NonPrecompact.BooleanBananaPositiveMassFinite
import Mathlib.Basic.Countable.Basic

/-!
# Countable positive-mass codes and arbitrary finite sizes

A code is a finite tuple of positive weights of total mass two. It
determines both the rational mass and the Boolean marking on all subsets.
Every positive-mass Boolean algebra is isomorphic to a coded powerset.
-/

namespace SuccessorTree.NonPrecompact.BooleanBanana

open scoped BigOperators Classical

/-- A finite positive-mass powerset code. -/
abbrev PositiveMassAtomCode (S : Set ℕ) :=
  {c : Σ n : ℕ, Fin n → PositiveMassWeight S // ∑ i, (c.2 i).mass = 2}

/-- Positive mass isomorphism types have a countable coding family. -/
theorem positiveMassAtomCode_countable (S : Set ℕ) : Countable (PositiveMassAtomCode S) := by
  letI : Countable (PositiveMassWeight S) := Function.Injective.countable (f := fun w : PositiveMassWeight S => (w.numerator, w.denominator))
    (fun x y h => by cases x; cases y; cases h; rfl)
  infer_instance

/-- Every code supplies a valid positive-mass finite powerset. -/
theorem positiveMassAtomCode_isFinite (S : Set ℕ) (c : PositiveMassAtomCode S) :
    IsFinitePositiveMass S
      (fun s : Finset (Fin c.1.1) => ∑ i ∈ s, (c.1.2 i).parity)
      (fun s : Finset (Fin c.1.1) => ∑ i ∈ s, (c.1.2 i).mass) :=
  weightedPowerset_isFinitePositiveMass c.1.2 c.2

/-- Every positive-mass marked Boolean algebra is isomorphic, with both
functions preserved on all elements, to one member of the coding family. -/
theorem positiveMassAtomCode_represents
    {A : Type*} [BooleanAlgebra A] [Fintype A]
    {S : Set ℕ} {μ : A → ZMod 2} {ρ : A → ℚ}
    (hA : IsFinitePositiveMass S μ ρ) :
    ∃ c : PositiveMassAtomCode S, ∃ e : A ≃o Finset (Fin c.1.1),
      (∀ x, (∑ i ∈ e x, (c.1.2 i).mass) = ρ x) ∧
      (∀ x, (∑ i ∈ e x, (c.1.2 i).parity) = μ x) := by
  classical
  obtain ⟨w, hwρ, hwμ⟩ := exists_positiveMass_atomCoordinates hA
  let eA := prebananaFiniteBooleanAtomFinsetOrderIso A
  let eI := Fintype.equivFin (PrebananaAbstractAtoms A)
  have htotal : ∑ i, (w (eI.symm i)).mass = 2 := by
    rw [eI.symm.sum_comp (fun a => (w a).mass)]
    have h := hwρ ⊤
    rw [eA.map_top, hA.mass_top] at h
    exact h
  let c : PositiveMassAtomCode S :=
    ⟨⟨Fintype.card (PrebananaAbstractAtoms A), fun i => w (eI.symm i)⟩, htotal⟩
  let eF : Finset (PrebananaAbstractAtoms A) ≃o Finset (Fin c.1.1) :=
    { toEquiv := eI.finsetCongr
      map_rel_iff' := by intro s t; change s.map _ ⊆ t.map _ ↔ s ⊆ t; simp }
  refine ⟨c, eA.trans eF, fun x => ?_, fun x => ?_⟩
  · change (∑ i ∈ (eA x).map eI.toEmbedding, (w (eI.symm i)).mass) = _
    rw [Finset.sum_map]
    simpa using hwρ x
  · change (∑ i ∈ (eA x).map eI.toEmbedding, (w (eI.symm i)).parity) = _
    rw [Finset.sum_map]
    simpa using hwμ x

/-- The allowed odd prime produces valid finite codes of arbitrarily
large atom count. -/
theorem positiveMassAtomCode_unbounded
    {S : Set ℕ} {p : ℕ} (hpS : p ∈ S) (hp : p.Prime) (hpOdd : Odd p) (n : ℕ) :
    ∃ c : PositiveMassAtomCode S, n ≤ c.1.1 := by
  let d := p ^ n
  have hd : d ∈ positiveMassDenominators S := by
    apply (positiveMassDenominators S).pow_mem
    exact ⟨hpOdd, fun q hq hdiv => ((Nat.prime_dvd_prime_iff_eq hq hp).mp hdiv).symm ▸ hpS⟩
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast (pow_pos hp.pos n).ne'
  let w : Fin (2 * d) → PositiveMassWeight S := fun _ => ⟨1, d, by decide, hd⟩
  have htotal : ∑ i, (w i).mass = 2 := by
    change (∑ _ : Fin (2 * d), (1 : ℚ) / (d : ℚ)) = _
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one_div]
    apply (div_eq_iff hd0).2
    push_cast
    rfl
  refine ⟨⟨⟨2 * d, w⟩, htotal⟩, ?_⟩
  change n ≤ 2 * d
  have hnd : n ≤ d := (Nat.lt_pow_self hp.one_lt).le
  omega

end SuccessorTree.NonPrecompact.BooleanBanana
