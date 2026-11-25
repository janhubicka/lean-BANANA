import BANANA.NonPrecompact.PrebananaFiniteBooleanCoordinates
import BANANA.NonPrecompact.BooleanBananaPositiveMassWeights
import BANANA.NonPrecompact.BooleanBananaPositiveMassUniformAtoms
import Mathlib.Data.Finset.Grade

/-!
# Positive-mass expansions on actual finite Boolean algebras

The presentation uses the canonical finite atom coordinates of Mathlib.
A mass and its marking are disjoint additive, have totals two and zero,
and each original atom has a positive fraction with an allowed denominator
and the prescribed parity. The atom condition implies the corresponding
fraction and parity condition on every Boolean element.
-/

namespace SuccessorTree.NonPrecompact.BooleanBanana

open scoped BigOperators Classical

/-- The manuscript's positive mass and its underlying admissible marking. -/
structure IsFinitePositiveMass {A : Type*} [BooleanAlgebra A]
    (S : Set ℕ) (μ : A → ZMod 2) (ρ : A → ℚ) : Prop where
  mass_bot : ρ ⊥ = 0
  mass_top : ρ ⊤ = 2
  mass_add : ∀ x y, x ⊓ y = ⊥ → ρ (x ⊔ y) = ρ x + ρ y
  mark_bot : μ ⊥ = 0
  mark_top : μ ⊤ = 0
  mark_add : ∀ x y, x ⊓ y = ⊥ → μ (x ⊔ y) = μ x + μ y
  atom : ∀ x, IsAtom x → ∃ w : PositiveMassWeight S, w.mass = ρ x ∧ w.parity = μ x

/-- General finite additivity in the previously checked powerset coordinates.
This applies to rational masses as well as to F₂ markings. -/
theorem finiteBoolean_additive_sum
    {A R : Type*} [BooleanAlgebra A] [Fintype A] [AddCommMonoid R]
    (ν : A → R) (hzero : ν ⊥ = 0)
    (hadd : ∀ x y, x ⊓ y = ⊥ → ν (x ⊔ y) = ν x + ν y) (x : A) :
    let e := prebananaFiniteBooleanAtomFinsetOrderIso A
    ν x = ∑ a ∈ e x, ν (e.symm {a}) := by
  classical
  let e := prebananaFiniteBooleanAtomFinsetOrderIso A
  simpa using (finiteAtomSum e ν hzero (fun a b hab => hadd a b hab.eq_bot)
    (e x)).symm

/-- Choose one positive weight for each atom. The sums reproduce both
functions on every element of the original finite algebra. -/
theorem exists_positiveMass_atomCoordinates
    {A : Type*} [BooleanAlgebra A] [Fintype A]
    {S : Set ℕ} {μ : A → ZMod 2} {ρ : A → ℚ}
    (h : IsFinitePositiveMass S μ ρ) :
    ∃ w : PrebananaAbstractAtoms A → PositiveMassWeight S,
      (∀ x, (∑ a ∈ prebananaFiniteBooleanAtomFinsetOrderIso A x, (w a).mass) = ρ x) ∧
      (∀ x, (∑ a ∈ prebananaFiniteBooleanAtomFinsetOrderIso A x, (w a).parity) = μ x) := by
  classical
  let e := prebananaFiniteBooleanAtomFinsetOrderIso A
  have hw (a : PrebananaAbstractAtoms A) :=
    h.atom (e.symm {a}) ((e.symm.isAtom_iff _).mpr (Finset.isAtom_singleton a))
  choose w hw using hw
  refine ⟨w, fun x => ?_, fun x => ?_⟩
  · rw [finiteBoolean_additive_sum ρ h.mass_bot h.mass_add x]
    exact Finset.sum_congr rfl (fun a _ => (hw a).1)
  · rw [finiteBoolean_additive_sum μ h.mark_bot h.mark_add x]
    exact Finset.sum_congr rfl (fun a _ => (hw a).2)

/-- A finite family of weighted atoms has a common odd denominator. -/
theorem exists_positiveMass_weight_numerators {I : Type*} [Fintype I]
    {S : Set ℕ} (w : I → PositiveMassWeight S) :
    ∃ d : ℕ, ∃ n : I → ℕ, d ∈ positiveMassDenominators S ∧
      ∀ i, 0 < n i ∧ (n i : ℚ) / (d : ℚ) = (w i).mass ∧
        (n i : ZMod 2) = (w i).parity :=
  exists_common_positive_mass_denominator (fun i => (w i).numerator)
    (fun i => (w i).denominator) (fun i => (w i).positive) (fun i => (w i).allowed)

/-- Finite sums of the weighted atoms are still fractions over the allowed
odd denominators, with the expected reduction modulo two. -/
theorem exists_positiveMass_weight_sum_fraction {I : Type*} [Fintype I]
    {S : Set ℕ} (w : I → PositiveMassWeight S) (s : Finset I) :
    ∃ d n : ℕ, d ∈ positiveMassDenominators S ∧
      (n : ℚ) / (d : ℚ) = ∑ i ∈ s, (w i).mass ∧
      (n : ZMod 2) = ∑ i ∈ s, (w i).parity := by
  obtain ⟨d, n, hd, hn⟩ := exists_positiveMass_weight_numerators w
  refine ⟨d, ∑ i ∈ s, n i, hd, ?_, ?_⟩
  · rw [Nat.cast_sum, Finset.sum_div]
    exact Finset.sum_congr rfl (fun i _ => (hn i).2.1)
  · rw [Nat.cast_sum]
    exact Finset.sum_congr rfl (fun i _ => (hn i).2.2)

/-- Every Boolean element has the claimed fraction and parity. The
numerator may be zero at bottom. -/
theorem positiveMass_element_fraction
    {A : Type*} [BooleanAlgebra A] [Fintype A]
    {S : Set ℕ} {μ : A → ZMod 2} {ρ : A → ℚ}
    (h : IsFinitePositiveMass S μ ρ) (x : A) :
    ∃ d n : ℕ, d ∈ positiveMassDenominators S ∧
      (n : ℚ) / (d : ℚ) = ρ x ∧ (n : ZMod 2) = μ x := by
  obtain ⟨w, hρ, hμ⟩ := exists_positiveMass_atomCoordinates h
  simpa only [hρ x, hμ x] using
    exists_positiveMass_weight_sum_fraction w (prebananaFiniteBooleanAtomFinsetOrderIso A x)

/-- Therefore a mass-preserving map between such finite algebras also
preserves the underlying marking. -/
theorem positiveMass_preserves_mark
    {A B : Type*} [BooleanAlgebra A] [Fintype A] [BooleanAlgebra B] [Fintype B]
    {S T : Set ℕ} {μ : A → ZMod 2} {ρ : A → ℚ} {ν : B → ZMod 2} {σ : B → ℚ}
    (hA : IsFinitePositiveMass S μ ρ) (hB : IsFinitePositiveMass T ν σ)
    (f : A → B) (hf : ∀ x, σ (f x) = ρ x) :
    ∀ x, ν (f x) = μ x := by
  intro x
  obtain ⟨d, a, hd, ha, hpa⟩ := positiveMass_element_fraction hA x
  obtain ⟨e, b, he, hb, hpb⟩ := positiveMass_element_fraction hB (f x)
  rw [← hpa, ← hpb]
  exact positiveMass_odd_fraction_parity he.1 hd.1 (hb.trans ((hf x).trans ha.symm))

/-- Any finite weighted powerset of total mass two is a positive-mass
expansion of its parity-marked Boolean algebra. -/
theorem weightedPowerset_isFinitePositiveMass {I : Type*} [Fintype I] [DecidableEq I]
    {S : Set ℕ} (w : I → PositiveMassWeight S)
    (htotal : (∑ i, (w i).mass) = 2) :
    IsFinitePositiveMass S
      (fun s : Finset I => ∑ i ∈ s, (w i).parity)
      (fun s : Finset I => ∑ i ∈ s, (w i).mass) := by
  have hm : (∑ i, (w i).parity) = 0 := by
    obtain ⟨d, n, hd, hn, hpn⟩ := exists_positiveMass_weight_sum_fraction w Finset.univ
    have hfrac : (n : ℚ) / (d : ℚ) = (2 : ℕ) / (1 : ℚ) := by
      rw [hn, htotal]
      simp
    have hp := positiveMass_odd_fraction_parity hd.1 odd_one hfrac
    rw [hpn] at hp
    exact hp.trans (by decide)
  constructor
  · exact Finset.sum_empty
  · exact htotal
  · intro x y h
    exact Finset.sum_union (Finset.disjoint_iff_inter_eq_empty.mpr h)
  · exact Finset.sum_empty
  · exact hm
  · intro x y h
    exact Finset.sum_union (Finset.disjoint_iff_inter_eq_empty.mpr h)
  · intro x hx
    obtain ⟨i, rfl⟩ := Finset.isAtom_iff.mp hx
    exact ⟨w i, by simp, by simp⟩

/-- The inverse-image map on finite powersets. -/
def positiveMassAtomPreimage {I J : Type*} [DecidableEq I] [DecidableEq J] [Fintype I] [Fintype J]
    (part : J → I) : BoundedLatticeHom (Finset I) (Finset J) where
  toFun s := Finset.univ.filter fun j => part j ∈ s
  map_bot' := by ext j; simp
  map_top' := by ext j; simp
  map_sup' s t := by ext j; simp
  map_inf' s t := by ext j; simp

theorem positiveMassAtomPreimage_injective {I J : Type*}
    [DecidableEq I] [DecidableEq J] [Fintype I] [Fintype J]
    {part : J → I} (hpart : Function.Surjective part) :
    Function.Injective (positiveMassAtomPreimage part) := by
  intro s t h
  ext i
  obtain ⟨j, rfl⟩ := hpart i
  have hj := congrArg (fun u : Finset J => j ∈ u) h
  simpa [positiveMassAtomPreimage] using hj

/-- A partition preserves a finitely additive weight exactly when the
weights agree on every atom fibre. -/
theorem positiveMassAtomPreimage_sum {I J R : Type*}
    [DecidableEq I] [DecidableEq J] [Fintype I] [Fintype J] [AddCommMonoid R]
    (part : J → I) (w : J → R) (s : Finset I) :
    ∑ j ∈ (positiveMassAtomPreimage part) s, w j =
      ∑ i ∈ s, ∑ j ∈ (Finset.univ.filter (fun j => part j = i)), w j :=
  (Finset.sum_fiberwise_eq_sum_filter Finset.univ s part w).symm

/-- Conjugation by the canonical atom coordinates transports any actual
finite Boolean-algebra embedding into a surjective atom partition. -/
theorem exists_positiveMass_atomPartition
    {A B : Type*} [BooleanAlgebra A] [Fintype A] [BooleanAlgebra B] [Fintype B]
    (f : BoundedLatticeHom A B) (hf : Function.Injective f) :
    ∃ part : PrebananaAbstractAtoms B → PrebananaAbstractAtoms A,
      Function.Surjective part ∧
      ∀ x, prebananaFiniteBooleanAtomFinsetOrderIso B (f x) =
        positiveMassAtomPreimage part (prebananaFiniteBooleanAtomFinsetOrderIso A x) := by
  classical
  obtain ⟨part, hsurj, hpart⟩ := prebanana_exists_atomPartition_of_powersetEmbedding
    (prebananaAbstractPowersetMap f)
    (prebananaAbstractPowersetMap_empty f (map_bot f))
    (prebananaAbstractPowersetMap_univ f (map_top f))
    (prebananaAbstractPowersetMap_union f (map_sup f))
    (prebananaAbstractPowersetMap_inter f (map_inf f))
    (prebananaAbstractPowersetMap_injective f hf)
  refine ⟨part, hsurj, fun x => ?_⟩
  have h := hpart (prebananaFiniteBooleanAtomFinsetOrderIso A x)
  simpa [prebananaAbstractPowersetMap, positiveMassAtomPreimage] using h

end SuccessorTree.NonPrecompact.BooleanBanana
