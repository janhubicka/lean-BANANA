import BANANA.NonPrecompact.BooleanBananaPadicChargeResidueApproximation
import BANANA.NonPrecompact.PrebananaResidueBlocks

/-!
# Realisation of two-adic residues on finite atom partitions

Use the established odd-subset-sum block assembly with one disjoint
batch for every atom except the last, and two reserved atoms for the
leftover block.
-/

namespace SuccessorTree.NonPrecompact.BooleanBanana

open Set
open scoped BigOperators

/-- The finite residue partitions needed for the charge flow exist. -/
theorem hasChargeResiduePartition : HasChargeResiduePartition := by
  classical
  intro m k z r hz htotal hr
  let J := ChargeAmbientIndex m k
  let q := 2 ^ (k + 1)
  let batch (i : Fin m) : Finset J :=
    Finset.univ.map
      ⟨fun j : Fin q => Sum.inl (i, j), fun _ _ h => (Prod.mk.inj (Sum.inl.inj h)).2⟩
  let reserve : Finset J := Finset.univ.map
    ⟨fun j : Fin 2 => Sum.inr j, fun _ _ h => Sum.inr.inj h⟩
  have hbcard (i : Fin m) : (batch i).card = 2 ^ (k + 1) := by
    simp [batch, q]
  have odd_weight (j : J) : Odd (z j).val := by
    apply ZMod.natCast_eq_one_iff_odd.mp
    have hdvd : 2 ∣ 2 ^ (k + 1) := by
      simpa using (pow_dvd_pow 2 (show 1 ≤ k + 1 by omega))
    rw [← ZMod.cast_natCast hdvd (z j).val, ZMod.natCast_zmod_val]
    exact hz j
  have hdisj : (Set.univ : Set (Fin m)).PairwiseDisjoint batch := by
    intro i _ i' _ hne
    change Disjoint (batch i) (batch i')
    rw [Finset.disjoint_left]
    intro j hj hj'
    obtain ⟨x, _, rfl⟩ := Finset.mem_map.mp hj
    obtain ⟨x', _, he⟩ := Finset.mem_map.mp hj'
    exact hne ((Prod.mk.inj (Sum.inl.inj he)).1.symm)
  have hresDisj (i : Fin m) : Disjoint reserve (batch i) := by
    rw [Finset.disjoint_left]
    intro j hj hj'
    obtain ⟨x, _, rfl⟩ := Finset.mem_map.mp hj
    obtain ⟨x', _, he⟩ := Finset.mem_map.mp hj'
    change (Sum.inl (i, x') : J) = Sum.inr x at he
    cases he
  have hresNonempty : reserve.Nonempty :=
    ⟨Sum.inr 0, Finset.mem_map.mpr ⟨0, Finset.mem_univ _, rfl⟩⟩
  have hrtotal :
      (∑ i : Fin m, r (Sum.inl i)) + r (Sum.inr ()) = 0 := by
    rw [Fintype.sum_sum_type] at hr
    simpa using hr
  obtain ⟨chosen, hchosen, hchosenDisjoint, hchosenSubset, _, hrestNonempty, hrestSum⟩ :=
    exists_prebanana_residue_block_assembly
      (k := k + 1) (m := m) (ι := J) (Finset.univ : Finset J) reserve batch
      (fun j => (z j).val) (fun i => r (Sum.inl i)) (r (Sum.inr ()))
      hbcard (fun _ j _ => odd_weight j)
      (fun _ => Finset.subset_univ _) hdisj
      hresNonempty (Finset.subset_univ _) hresDisj
      (by simpa only [ZMod.natCast_zmod_val] using htotal) hrtotal
  let selected := (Finset.univ : Finset (Fin m)).biUnion chosen
  let owner (j : J) : ChargeTargetIndex m :=
    if h : ∃ i, j ∈ chosen i then Sum.inl (Classical.choose h) else Sum.inr ()
  have hx (i : Fin m) (j : J) : owner j = Sum.inl i ↔ j ∈ chosen i := by
    by_cases hj : ∃ a, j ∈ chosen a
    · have hjc := Classical.choose_spec hj
      simp only [owner, dite_eq_left hj, Sum.inl.injEq]
      constructor
      · intro e
        simpa only [e] using hjc
      · intro hji
        by_contra hne
        have hd := hchosenDisjoint
          (Set.mem_univ (Classical.choose hj)) (Set.mem_univ i) hne
        exact Finset.disjoint_left.mp hd hjc hji
    · simp only [owner, dite_eq_right hj]
      constructor
      · intro h
        cases h
      · intro h
        exact False.elim (hj ⟨i, h⟩)
  have hy (j : J) : owner j = Sum.inr () ↔ j ∉ selected := by
    have hsel : j ∈ selected ↔ ∃ i, j ∈ chosen i := by
      simp [selected]
    rw [hsel]
    by_cases hj : ∃ a, j ∈ chosen a
    · simp [owner, dite_eq_left hj, hj]
    · simp [owner, dite_eq_right hj, hj]
  refine ⟨owner, ?_, ?_⟩
  · rintro (i | ⟨⟩)
    · obtain ⟨j, hj⟩ := (hchosen i).1
      exact ⟨j, (hx i j).2 hj⟩
    · obtain ⟨j, hj⟩ := hrestNonempty
      exact ⟨j, (hy j).2 (Finset.mem_sdiff.mp hj).2⟩
  · rintro (i | ⟨⟩)
    · have heq : Finset.univ.filter (fun j => owner j = Sum.inl i) = chosen i := by
        ext j
        simp [hx]
      rw [heq]
      simpa only [ZMod.natCast_zmod_val] using (hchosen i).2.2
    · have heq : Finset.univ.filter (fun j => owner j = Sum.inr ()) =
          Finset.univ \ selected := by
        ext j
        simp [hy]
      rw [heq]
      simpa only [ZMod.natCast_zmod_val] using hrestSum

variable {B : Type*} [BooleanAlgebra B] [Nontrivial B]

/-- All the residue approximations exist on a homogeneous marked algebra
with the stated all-marked finite ambients. -/
theorem dense_padicChargeOrbit_of_homogeneous_allMarked
    {mark : B → ZMod 2}
    (hamb : ∀ m k : ℕ,
      ∃ f : BoundedLatticeHom (Finset (ChargeAmbientIndex m k)) B,
        Function.Injective f ∧ ∀ j, mark (f {j}) = 1)
    (hhom : ∀ (S : BooleanSubalgebra B) [Fintype S]
      (f : BoundedLatticeHom S B), Function.Injective f →
        (∀ a : S, mark (f a) = mark a.val) →
        ∃ g : markedAutomorphisms mark, ∀ a : S, g.val.symm a.val = f a)
    (c : PadicCharge mark) :
    Dense (MulAction.orbit (markedAutomorphisms mark) c) :=
  dense_padicChargeOrbit_of_partitions hasChargeResiduePartition hamb hhom c

/-- On a countable homogeneous marked algebra with the required all-marked
finite ambients, every charge orbit is dense and meagre and no orbit is
comeagre. -/
theorem padicChargeOrbit_dense_meagre_of_homogeneous_allMarked [Countable B]
    {mark : B → ZMod 2}
    (hamb : ∀ m k : ℕ,
      ∃ f : BoundedLatticeHom (Finset (ChargeAmbientIndex m k)) B,
        Function.Injective f ∧ ∀ j, mark (f {j}) = 1)
    (hhom : ∀ (S : BooleanSubalgebra B) [Fintype S]
      (f : BoundedLatticeHom S B), Function.Injective f →
        (∀ a : S, mark (f a) = mark a.val) →
        ∃ g : markedAutomorphisms mark, ∀ a : S, g.val.symm a.val = f a)
    (c : PadicCharge mark) :
    Dense (MulAction.orbit (markedAutomorphisms mark) c) ∧
      IsMeagre (MulAction.orbit (markedAutomorphisms mark) c) ∧
      MulAction.orbit (markedAutomorphisms mark) c ∉ residual (PadicCharge mark) := by
  obtain ⟨a, ha, _⟩ := hamb 0 0
  let j : ChargeAmbientIndex 0 0 := Sum.inr 0
  let l : ChargeAmbientIndex 0 0 := Sum.inr 1
  have hnebot : a {j} ≠ ⊥ := by
    intro h
    have heq : a {j} = a (⊥ : Finset (ChargeAmbientIndex 0 0)) := by
      rw [map_bot]
      exact h
    exact Finset.singleton_ne_empty j (ha heq)
  have hnetop : a {j} ≠ ⊤ := by
    intro h
    have h' : ({j} : Finset (ChargeAmbientIndex 0 0)) = ⊤ :=
      ha (by rw [map_top]; exact h)
    have hj : l ∈ ({j} : Finset (ChargeAmbientIndex 0 0)) := by
      rw [h']
      exact Finset.mem_univ _
    exact (by decide : l ≠ j) (Finset.mem_singleton.mp hj)
  exact ⟨dense_padicChargeOrbit_of_homogeneous_allMarked hamb hhom c,
    padicChargeOrbit_meagre c hnebot hnetop⟩

end SuccessorTree.NonPrecompact.BooleanBanana
