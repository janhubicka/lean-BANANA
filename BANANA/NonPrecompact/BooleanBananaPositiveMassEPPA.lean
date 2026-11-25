import BANANA.NonPrecompact.BooleanBananaPositiveMassFinite

/-!
# EPPA for finite positive-mass Boolean–BANANA

One uniform refinement works simultaneously for all mass-preserving
partial isomorphisms. Partial maps are represented by two unital
embeddings of the same finite Boolean algebra; their ranges can be any
subalgebras of the original finite algebra.
-/

namespace SuccessorTree.NonPrecompact.BooleanBanana

open scoped BigOperators Classical

/-- A permutation of atoms induces an order automorphism of their
finite powerset, with identical cardinalities on every element. -/
def uniformPowersetOrderIso {I : Type*} [DecidableEq I]
    (π : Equiv.Perm I) : Finset I ≃o Finset I where
  toEquiv := π.finsetCongr
  map_rel_iff' := by
    intro s t
    change s.map π.toEmbedding ⊆ t.map π.toEmbedding ↔ s ⊆ t
    simp

@[simp]
theorem uniformPowersetOrderIso_card {I : Type*} [DecidableEq I]
    (π : Equiv.Perm I) (s : Finset I) :
    (uniformPowersetOrderIso π s).card = s.card :=
  Finset.card_map _

/-- The fibre map is read from the image of each original atom. -/
theorem positiveMass_atomPartition_sum
    {A B R : Type*} [BooleanAlgebra A] [Fintype A] [BooleanAlgebra B] [Fintype B]
    [AddCommMonoid R] (ρ : B → R)
    (w : PrebananaAbstractAtoms B → R)
    (hw : ∀ x, ρ x = ∑ b ∈ prebananaFiniteBooleanAtomFinsetOrderIso B x, w b)
    (f : BoundedLatticeHom A B)
    (part : PrebananaAbstractAtoms B → PrebananaAbstractAtoms A)
    (hpart : ∀ x, prebananaFiniteBooleanAtomFinsetOrderIso B (f x) =
      positiveMassAtomPreimage part (prebananaFiniteBooleanAtomFinsetOrderIso A x)) (a : PrebananaAbstractAtoms A) :
    (∑ b ∈ Finset.univ.filter (fun b => part b = a), w b) =
      ρ (f ((prebananaFiniteBooleanAtomFinsetOrderIso A).symm {a})) := by
  rw [hw, hpart, OrderIso.apply_symm_apply]
  simp [positiveMassAtomPreimage]

/-- EPPA for the actual finite positive-mass algebras. The witness has
uniform atom weights. Every pair of embeddings describing a mass-preserving
partial automorphism extends to one weight- and marking-preserving
automorphism of this same finite witness. -/
theorem positiveMass_eppa
    {A : Type} [BooleanAlgebra A] [Fintype A]
    {S : Set ℕ} {μ : A → ZMod 2} {ρ : A → ℚ}
    (hA : IsFinitePositiveMass S μ ρ) :
    ∃ d : ℕ, ∃ n : PrebananaAbstractAtoms A → ℕ, d ∈ positiveMassDenominators S ∧
      (∀ a, 0 < n a) ∧ (∑ a, n a) = 2 * d ∧
      let J := Σ a, Fin (n a)
      IsFinitePositiveMass S (fun s : Finset J => (s.card : ZMod 2))
        (fun s : Finset J => (s.card : ℚ) / (d : ℚ)) ∧
      ∃ f : BoundedLatticeHom A (Finset J),
        Function.Injective f ∧
        (∀ x, ((f x).card : ℚ) / (d : ℚ) = ρ x ∧ ((f x).card : ZMod 2) = μ x) ∧
        ∀ (C : Type) [BooleanAlgebra C] [Fintype C]
          (p q : BoundedLatticeHom C A),
          Function.Injective p → Function.Injective q →
          (∀ c, ρ (p c) = ρ (q c)) →
          ∃ e : Finset J ≃o Finset J,
            (∀ s, ((e s).card : ℚ) / (d : ℚ) = (s.card : ℚ) / (d : ℚ) ∧
              ((e s).card : ZMod 2) = (s.card : ZMod 2)) ∧
            ∀ c, e (f (p c)) = f (q c) := by
  classical
  obtain ⟨w, hwρ, hwμ⟩ := exists_positiveMass_atomCoordinates hA
  obtain ⟨d, n, hd, hn⟩ := exists_positiveMass_weight_numerators w
  have hd0 : d ≠ 0 := by
    obtain ⟨k, hk⟩ := hd.1
    omega
  have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast hd0
  let I := PrebananaAbstractAtoms A
  let J := Σ a, Fin (n a)
  let eA := prebananaFiniteBooleanAtomFinsetOrderIso A
  have hρ (x : A) : (∑ a ∈ eA x, (n a : ℚ) / (d : ℚ)) = ρ x := by
    rw [← hwρ x]
    exact Finset.sum_congr rfl (fun a _ => (hn a).2.1)
  have hμ (x : A) : (∑ a ∈ eA x, (n a : ZMod 2)) = μ x := by
    rw [← hwμ x]
    exact Finset.sum_congr rfl (fun a _ => (hn a).2.2)
  have htotal : (∑ a, n a) = 2 * d := by
    have h := hρ ⊤
    rw [eA.map_top, ← Finset.sum_div, ← Nat.cast_sum, hA.mass_top] at h
    exact_mod_cast (div_eq_iff hdQ).mp h
  let unitWeight : J → PositiveMassWeight S := fun _ => ⟨1, d, by decide, hd⟩
  have hw : (∑ j : J, (unitWeight j).mass) = 2 := by
    change (∑ _ : J, (1 : ℚ) / (d : ℚ)) = 2
    have hcard : Fintype.card J = 2 * d := by
      change Fintype.card (Σ a, Fin (n a)) = _
      simpa [Fintype.card_sigma] using htotal
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard, mul_one_div]
    apply (div_eq_iff hdQ).2
    push_cast
    rfl
  have hmodel := weightedPowerset_isFinitePositiveMass unitWeight hw
  have hm₁ (s : Finset J) :
      (∑ j ∈ s, (unitWeight j).mass) = (s.card : ℚ) / (d : ℚ) := by
    change (∑ _ ∈ s, (1 : ℚ) / (d : ℚ)) = _
    simp [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
  have hm₂ (s : Finset J) :
      (∑ j ∈ s, (unitWeight j).parity) = (s.card : ZMod 2) := by
    change (∑ _ ∈ s, (1 : ZMod 2)) = _
    simp
  have hmodel' :
      IsFinitePositiveMass S (fun s : Finset J => (s.card : ZMod 2))
        (fun s : Finset J => (s.card : ℚ) / (d : ℚ)) := by
    rw [show (fun s : Finset J => (s.card : ZMod 2)) =
      (fun s => ∑ j ∈ s, (unitWeight j).parity) from (funext hm₂).symm]
    rw [show (fun s : Finset J => (s.card : ℚ) / (d : ℚ)) =
      (fun s => ∑ j ∈ s, (unitWeight j).mass) from (funext hm₁).symm]
    exact hmodel
  let f : BoundedLatticeHom A (Finset J) :=
    (positiveMassAtomPreimage (Sigma.fst : J → I)).comp eA
  have hf : Function.Injective f :=
    (positiveMassAtomPreimage_injective (uniform_atom_refinement_surjective n
      (fun a => (hn a).1))).comp eA.injective
  have hpres (x : A) : ((f x).card : ℚ) / (d : ℚ) = ρ x ∧
      ((f x).card : ZMod 2) = μ x := by
    have h := uniform_atom_refinement_preserves n d (eA x)
    change (((f x).card : ℚ) / (d : ℚ) = _) ∧ ((f x).card : ZMod 2) = _ at h
    rw [hρ, hμ] at h
    exact h
  refine ⟨d, n, hd, fun a => (hn a).1, htotal, hmodel', f, hf, hpres, ?_⟩
  intro C _ _ p q hp hq hmass
  obtain ⟨s, hs, hsp⟩ := exists_positiveMass_atomPartition p hp
  obtain ⟨t, ht, htq⟩ := exists_positiveMass_atomPartition q hq
  have hblocks (j : PrebananaAbstractAtoms C) :
      (∑ a ∈ Finset.univ.filter (fun a => s a = j), (n a : ℚ) / (d : ℚ)) =
        ∑ a ∈ Finset.univ.filter (fun a => t a = j), (n a : ℚ) / (d : ℚ) := by
    rw [positiveMass_atomPartition_sum ρ _ (fun x => (hρ x).symm) p s hsp,
      positiveMass_atomPartition_sum ρ _ (fun x => (hρ x).symm) q t htq]
    exact hmass _
  obtain ⟨π, hπ⟩ := exists_uniform_atom_permutation n hd0 s t hblocks
  let e := uniformPowersetOrderIso π
  refine ⟨e, fun u => by simp [e], fun c => ?_⟩
  ext j
  have hπj := hπ (π.symm j)
  rw [π.apply_symm_apply] at hπj
  change j ∈ (f (p c)).map π.toEmbedding ↔ j ∈ f (q c)
  rw [Finset.mem_map_equiv]
  change π.symm j ∈ positiveMassAtomPreimage (Sigma.fst : J → I) (eA (p c)) ↔
    j ∈ positiveMassAtomPreimage (Sigma.fst : J → I) (eA (q c))
  rw [show eA (p c) = _ from hsp c, show eA (q c) = _ from htq c]
  simp [positiveMassAtomPreimage, hπj]

end SuccessorTree.NonPrecompact.BooleanBanana
