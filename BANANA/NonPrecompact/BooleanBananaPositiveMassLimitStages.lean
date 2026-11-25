import BANANA.NonPrecompact.BooleanBananaPositiveMassEPPA
import BANANA.NonPrecompact.BooleanBananaPositiveMassStages

/-!
# Finite extension into a uniform positive-mass tower

A common denominator for a finite positive-mass algebra can be increased to
any allowed multiple. The resulting integer atom weights give an embedding
into the uniform powerset at that denominator. An atom permutation aligns
any two embeddings which agree on masses, giving the finite extension
property of a cofinal uniformly refined tower.
-/

namespace SuccessorTree.NonPrecompact.BooleanBanana

open scoped BigOperators Classical

/-- A uniform stage with `2*d` atoms is itself an allowed positive-mass model. -/
theorem positiveMass_uniformStage {J : Type*} [Fintype J] [DecidableEq J]
    {S : Set ℕ} {d : ℕ} (hd : d ∈ positiveMassDenominators S)
    (hJ : Fintype.card J = 2 * d) :
    IsFinitePositiveMass S (fun s : Finset J => (s.card : ZMod 2))
      (fun s : Finset J => (s.card : ℚ) / (d : ℚ)) := by
  have hd0 : (d : ℚ) ≠ 0 := by
    obtain ⟨k, hk⟩ := hd.1
    exact_mod_cast (show d ≠ 0 by omega)
  let w : J → PositiveMassWeight S := fun _ => ⟨1, d, by decide, hd⟩
  have ht : (∑ i, (w i).mass) = 2 := by
    change (∑ _ : J, (1 : ℚ) / (d : ℚ)) = _
    rw [Finset.sum_const, Finset.card_univ, hJ, nsmul_eq_mul, mul_one_div]
    apply (div_eq_iff hd0).mpr
    push_cast
    rfl
  have hm (s : Finset J) : (∑ j ∈ s, (w j).mass) = (s.card : ℚ) / (d : ℚ) := by
    change (∑ _ ∈ s, (1 : ℚ) / (d : ℚ)) = _
    simp [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
  have hμ (s : Finset J) : (∑ j ∈ s, (w j).parity) = (s.card : ZMod 2) := by
    change (∑ _ ∈ s, (1 : ZMod 2)) = _
    simp
  simpa only [funext hm, funext hμ] using weightedPowerset_isFinitePositiveMass w ht

/-- Every allowed finite model embeds in any uniform stage whose denominator
is an allowed multiple of one common denominator for the model. -/
theorem exists_positiveMass_uniformStageEmbedding
    {B : Type*} [BooleanAlgebra B] [Fintype B]
    {S : Set ℕ} {μ : B → ZMod 2} {ρ : B → ℚ} (hB : IsFinitePositiveMass S μ ρ) :
    ∃ d ∈ positiveMassDenominators S,
    ∀ (J : Type*) [Fintype J] [DecidableEq J] (D : ℕ),
      D ∈ positiveMassDenominators S → d ∣ D → Fintype.card J = 2 * D →
      ∃ f : BoundedLatticeHom B (Finset J), Function.Injective f ∧
        (∀ b, ((f b).card : ℚ) / (D : ℚ) = ρ b ∧ ((f b).card : ZMod 2) = μ b) := by
  classical
  obtain ⟨w, hwρ, hwμ⟩ := exists_positiveMass_atomCoordinates hB
  obtain ⟨d, n, hd, hn⟩ := exists_positiveMass_weight_numerators w
  refine ⟨d, hd, ?_⟩
  intro J _ _ D hD hdD hJ
  obtain ⟨k, hk⟩ := hdD
  have hdpos : 0 < d := by
    obtain ⟨a, ha⟩ := hd.1
    omega
  have hDpos : 0 < D := by
    obtain ⟨a, ha⟩ := hD.1
    omega
  have hkpos : 0 < k := by
    by_contra! h
    rw [Nat.eq_zero_of_le_zero h, mul_zero] at hk
    omega
  have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast hkpos.ne'
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hdpos.ne'
  have hD0 : (D : ℚ) ≠ 0 := by exact_mod_cast hDpos.ne'
  let I := PrebananaAbstractAtoms B
  let a (i : I) := n i * k
  let eB := prebananaFiniteBooleanAtomFinsetOrderIso B
  have hfrac (i : I) : (a i : ℚ) / (D : ℚ) = (w i).mass := by
    rw [← (hn i).2.1, hk]
    change ((n i * k : ℕ) : ℚ) / ((d * k : ℕ) : ℚ) = _
    push_cast
    exact mul_div_mul_right _ _ hk0
  have hρ (b : B) : (∑ i ∈ eB b, (a i : ℚ) / (D : ℚ)) = ρ b := by
    rw [← hwρ b]
    exact Finset.sum_congr rfl (fun i _ => hfrac i)
  have htotal : (∑ i, a i) = 2 * D := by
    have h := hρ ⊤
    rw [eB.map_top, ← Finset.sum_div, ← Nat.cast_sum, hB.mass_top] at h
    exact_mod_cast (div_eq_iff hD0).mp h
  let K := Σ i : I, Fin (a i)
  have hcard : Fintype.card K = Fintype.card J := by
    change Fintype.card (Σ i : I, Fin (a i)) = _
    rw [Fintype.card_sigma, hJ]
    simpa only [Fintype.card_fin] using htotal
  let e := Fintype.equivOfCardEq hcard
  let part : J → I := fun j => (e.symm j).1
  have hsurj : Function.Surjective part := by
    intro i
    obtain ⟨z, hz⟩ := uniform_atom_refinement_surjective a
      (fun i => Nat.mul_pos (hn i).1 hkpos) i
    exact ⟨e z, by simp [part, hz]⟩
  let f : BoundedLatticeHom B (Finset J) :=
    (positiveMassAtomPreimage part).comp (eB : BoundedLatticeHom B (Finset I))
  have hf : Function.Injective f :=
    (positiveMassAtomPreimage_injective hsurj).comp eB.injective
  have hcard_f (b : B) :
      (f b).card = (Finset.univ.filter (fun z : K => z.1 ∈ eB b)).card := by
    have heq : (f b) = (Finset.univ.filter (fun z : K => z.1 ∈ eB b)).map e.toEmbedding := by
      ext j
      simp [f, part, positiveMassAtomPreimage, Finset.mem_map_equiv]
    rw [heq, Finset.card_map]
  have hmass (b : B) : ((f b).card : ℚ) / (D : ℚ) = ρ b := by
    rw [hcard_f b]
    exact (uniform_atom_refinement_preserves a D (eB b)).1.trans (hρ b)
  exact ⟨f, hf, fun b => ⟨hmass b,
    positiveMass_preserves_mark hB (positiveMass_uniformStage hD hJ) f hmass b⟩⟩

/-- Two injective embeddings into a uniform finite powerset with equal
cardinalities of the images differ by a permutation of its atoms. -/
theorem exists_uniformStage_permutation
    {A J : Type*} [BooleanAlgebra A] [Fintype A] [Fintype J] [DecidableEq J]
    (f g : BoundedLatticeHom A (Finset J))
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hcard : ∀ a, (f a).card = (g a).card) :
    ∃ π : Equiv.Perm J, ∀ a, uniformPowersetOrderIso π (f a) = g a := by
  classical
  let eA := prebananaFiniteBooleanAtomFinsetOrderIso A
  let f' : BoundedLatticeHom (Finset (PrebananaAbstractAtoms A)) (Finset J) :=
    f.comp eA.symm
  let g' : BoundedLatticeHom (Finset (PrebananaAbstractAtoms A)) (Finset J) :=
    g.comp eA.symm
  obtain ⟨q, hq, hpartq⟩ := prebanana_exists_atomPartition_of_powersetEmbedding
    f' (map_bot f') (map_top f') (map_sup f') (map_inf f') (hf.comp eA.symm.injective)
  obtain ⟨r, hr, hpartr⟩ := prebanana_exists_atomPartition_of_powersetEmbedding
    g' (map_bot g') (map_top g') (map_sup g') (map_inf g') (hg.comp eA.symm.injective)
  have hsize (i : PrebananaAbstractAtoms A) :
      Fintype.card {j : J // q j = i} = Fintype.card {j : J // r j = i} := by
    rw [Fintype.card_subtype, Fintype.card_subtype]
    have h := hcard (eA.symm {i})
    change (f' {i}).card = (g' {i}).card at h
    rw [hpartq {i}, hpartr {i}] at h
    simpa only [Finset.mem_singleton] using h
  let block (i : PrebananaAbstractAtoms A) := Fintype.equivOfCardEq (hsize i)
  let π := Equiv.ofFiberEquiv block
  have hπ (j : J) : r (π j) = q j := Equiv.ofFiberEquiv_map block j
  refine ⟨π, fun a => ?_⟩
  have hf'' : f a = Finset.univ.filter (fun j => q j ∈ eA a) := by
    simpa [f'] using hpartq (eA a)
  have hg'' : g a = Finset.univ.filter (fun j => r j ∈ eA a) := by
    simpa [g'] using hpartr (eA a)
  rw [hf'', hg'']
  ext j
  have h := hπ (π.symm j)
  rw [π.apply_symm_apply] at h
  change j ∈ (Finset.univ.filter fun j => q j ∈ eA a).map π.toEmbedding ↔
    j ∈ Finset.univ.filter (fun j => r j ∈ eA a)
  simp only [Finset.mem_map_equiv, Finset.mem_filter, Finset.mem_univ, true_and, h]

/-- Cofinality in allowed denominators yields the genuine finite extension
property into uniform stages. The supplied stage maps need only be
mass-preserving Boolean embeddings. -/
theorem positiveMass_uniformTower_extension
    {S : Set ℕ} (D : ℕ → ℕ) (hD : ∀ n, D n ∈ positiveMassDenominators S)
    (hdiv : ∀ m n, m ≤ n → D m ∣ D n)
    (hcofinal : ∀ d ∈ positiveMassDenominators S, ∃ n, d ∣ D n)
    (J : ℕ → Type) [∀ n, Fintype (J n)] [∀ n, DecidableEq (J n)]
    (hcard : ∀ n, Fintype.card (J n) = 2 * D n)
    (lift : ∀ m n, m ≤ n → BoundedLatticeHom (Finset (J m)) (Finset (J n)))
    (hlift : ∀ m n h, Function.Injective (lift m n h))
    (hmass : ∀ m n h x, ((lift m n h x).card : ℚ) / (D n : ℚ) = (x.card : ℚ) / (D m : ℚ))
    {A B : Type} [BooleanAlgebra A] [Fintype A] [BooleanAlgebra B] [Fintype B]
    {μB : B → ZMod 2} {ρB : B → ℚ} (hB : IsFinitePositiveMass S μB ρB)
    (m : ℕ) (f : BoundedLatticeHom A B) (hf : Function.Injective f)
    (g : BoundedLatticeHom A (Finset (J m))) (hg : Function.Injective g)
    (hpres : ∀ a, ρB (f a) = ((g a).card : ℚ) / (D m : ℚ)) :
    ∃ n : ℕ, ∃ hmn : m ≤ n,
      ∃ e : BoundedLatticeHom B (Finset (J n)),
        Function.Injective e ∧
        (∀ b, ((e b).card : ℚ) / (D n : ℚ) = ρB b ∧ ((e b).card : ZMod 2) = μB b) ∧
        ∀ a, e (f a) = lift m n hmn (g a) := by
  classical
  obtain ⟨d, hd, hEmb⟩ := exists_positiveMass_uniformStageEmbedding hB
  obtain ⟨l, hl⟩ := hcofinal d hd
  let n := max m l
  have hmn : m ≤ n := le_max_left _ _
  obtain ⟨e, he, hE⟩ := hEmb (J n) (D n) (hD n)
    (hl.trans (hdiv l n (le_max_right _ _))) (hcard n)
  let u := e.comp f
  let v := (lift m n hmn).comp g
  have hDn : (D n : ℚ) ≠ 0 := by
    obtain ⟨k, hk⟩ := (hD n).1
    exact_mod_cast (show D n ≠ 0 by omega)
  have hsame (a : A) : (u a).card = (v a).card := by
    apply Nat.cast_injective (R := ℚ)
    apply (div_left_inj' hDn).mp
    calc
      ((u a).card : ℚ) / (D n : ℚ) = ρB (f a) := (hE _).1
      _ = ((g a).card : ℚ) / (D m : ℚ) := hpres a
      _ = ((v a).card : ℚ) / (D n : ℚ) := (hmass m n hmn (g a)).symm
  obtain ⟨π, hπ⟩ := exists_uniformStage_permutation u v (he.comp hf)
    ((hlift m n hmn).comp hg) hsame
  let e' : BoundedLatticeHom B (Finset (J n)) :=
    (uniformPowersetOrderIso π : BoundedLatticeHom (Finset (J n)) (Finset (J n))).comp e
  refine ⟨n, hmn, e', (uniformPowersetOrderIso π).injective.comp he, ?_, hπ⟩
  intro b
  change (((uniformPowersetOrderIso π) (e b)).card : ℚ) / (D n : ℚ) = ρB b ∧
    (((uniformPowersetOrderIso π) (e b)).card : ZMod 2) = μB b
  simpa only [uniformPowersetOrderIso_card] using hE b

end SuccessorTree.NonPrecompact.BooleanBanana
