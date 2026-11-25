import BANANA.NonPrecompact.BooleanBananaPositiveMassEPPA
import BANANA.NonPrecompact.BooleanBananaPositiveMassAmalgam
import BANANA.NonPrecompact.FiberGridFibreEquivs

/-!
# Strong amalgamation for the actual finite positive-mass class

The known weighted grid is transported through the canonical atom
partitions of arbitrary finite Boolean embeddings. The resulting common
extension is itself a positive-mass Boolean algebra, and its two
embedded subalgebras intersect precisely in the original common base.
-/

namespace SuccessorTree.NonPrecompact.BooleanBanana

open scoped BigOperators Classical

set_option maxHeartbeats 800000 in
/-- Strong amalgamation on the original finite Boolean carriers, with
both rational mass and parity preserved on every Boolean element. -/
theorem positiveMass_strongAmalgamation
    {A B C : Type} [BooleanAlgebra A] [Fintype A] [BooleanAlgebra B] [Fintype B]
    [BooleanAlgebra C] [Fintype C]
    {S : Set ℕ} {p : ℕ} (hpS : p ∈ S) (hp : p.Prime) (hpOdd : Odd p)
    {μA : A → ZMod 2} {ρA : A → ℚ}
    {μB : B → ZMod 2} {ρB : B → ℚ}
    {μC : C → ZMod 2} {ρC : C → ℚ}
    (hA : IsFinitePositiveMass S μA ρA) (hB : IsFinitePositiveMass S μB ρB)
    (hC : IsFinitePositiveMass S μC ρC)
    (f : BoundedLatticeHom A B) (g : BoundedLatticeHom A C)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hfρ : ∀ a, ρB (f a) = ρA a) (hgρ : ∀ a, ρC (g a) = ρA a) :
    ∃ (I : Type) (finI : Fintype I) (eqI : DecidableEq I),
      letI := finI
      letI := eqI
      ∃ (μD : Finset I → ZMod 2) (ρD : Finset I → ℚ),
        IsFinitePositiveMass S μD ρD ∧
        ∃ (i : BoundedLatticeHom B (Finset I)) (j : BoundedLatticeHom C (Finset I)),
          Function.Injective i ∧ Function.Injective j ∧
          (∀ b, ρD (i b) = ρB b ∧ μD (i b) = μB b) ∧
          (∀ c, ρD (j c) = ρC c ∧ μD (j c) = μC c) ∧
          (∀ a, i (f a) = j (g a)) ∧
          (∀ b c, i b = j c → ∃ a, f a = b ∧ g a = c) := by
  classical
  obtain ⟨wB, hwB, _⟩ := exists_positiveMass_atomCoordinates hB
  obtain ⟨wC, hwC, _⟩ := exists_positiveMass_atomCoordinates hC
  obtain ⟨partB, hsurjB, hpartB⟩ := exists_positiveMass_atomPartition f hf
  obtain ⟨partC, hsurjC, hpartC⟩ := exists_positiveMass_atomPartition g hg
  let eA := prebananaFiniteBooleanAtomFinsetOrderIso A
  let eB := prebananaFiniteBooleanAtomFinsetOrderIso B
  let eC := prebananaFiniteBooleanAtomFinsetOrderIso C
  have hbase (a : PrebananaAbstractAtoms A) :
      (∑ b : LeftFiber partB a, (wB b.1).mass) =
        ∑ c : RightFiber partC a, (wC c.1).mass := by
    rw [← Finset.sum_subtype (p := fun b => partB b = a)
      (Finset.univ.filter (fun b => partB b = a)) (fun b => by simp) (fun b => (wB b).mass),
      ← Finset.sum_subtype (p := fun c => partC c = a)
      (Finset.univ.filter (fun c => partC c = a)) (fun c => by simp) (fun c => (wC c).mass)]
    rw [positiveMass_atomPartition_sum ρB _ (fun x => (hwB x).symm) f partB hpartB,
      positiveMass_atomPartition_sum ρC _ (fun x => (hwC x).symm) g partC hpartC,
      hfρ, hgρ]
  obtain ⟨wD, hL, hR, hcomm, hrow, hcol, hinter⟩ :=
    exists_positive_mass_strong_amalgam hpS hp hpOdd partB partC hsurjB hsurjC wB wC hbase
  let I := FiberGrid partB partC
  let projL (x : I) := x.2.1.1
  let projR (x : I) := x.2.2.1
  let i : BoundedLatticeHom B (Finset I) :=
    (positiveMassAtomPreimage projL).comp eB
  let j : BoundedLatticeHom C (Finset I) :=
    (positiveMassAtomPreimage projR).comp eC
  have hi : Function.Injective i :=
    (positiveMassAtomPreimage_injective hL).comp eB.injective
  have hj : Function.Injective j :=
    (positiveMassAtomPreimage_injective hR).comp eC.injective
  have hrow' (b : PrebananaAbstractAtoms B) :
      (∑ x ∈ Finset.univ.filter (fun x : I => projL x = b), (wD x).mass) = (wB b).mass := by
    rw [Finset.sum_subtype (p := fun x : I => projL x = b) _ (fun x => by simp)]
    rw [← Fintype.sum_equiv (fiberGridRowSubtypeEquiv partB partC b)
      _ (fun x => (wD x.1).mass) (fun _ => rfl)]
    exact (hrow b).1
  have hcol' (c : PrebananaAbstractAtoms C) :
      (∑ x ∈ Finset.univ.filter (fun x : I => projR x = c), (wD x).mass) = (wC c).mass := by
    rw [Finset.sum_subtype (p := fun x : I => projR x = c) _ (fun x => by simp)]
    rw [← Fintype.sum_equiv (fiberGridColumnSubtypeEquiv partB partC c)
      _ (fun x => (wD x.1).mass) (fun _ => rfl)]
    exact (hcol c).1
  let ρD (s : Finset I) := ∑ x ∈ s, (wD x).mass
  let μD (s : Finset I) := ∑ x ∈ s, (wD x).parity
  have hiρ (b : B) : ρD (i b) = ρB b := by
    change (∑ x ∈ positiveMassAtomPreimage projL (eB b), (wD x).mass) = _
    rw [positiveMassAtomPreimage_sum, ← hwB b]
    exact Finset.sum_congr rfl (fun a _ => hrow' a)
  have hjρ (c : C) : ρD (j c) = ρC c := by
    change (∑ x ∈ positiveMassAtomPreimage projR (eC c), (wD x).mass) = _
    rw [positiveMassAtomPreimage_sum, ← hwC c]
    exact Finset.sum_congr rfl (fun a _ => hcol' a)
  have htotal : ∑ x : I, (wD x).mass = 2 := by
    have h := hiρ ⊤
    rw [map_top, hB.mass_top] at h
    exact h
  have hD : IsFinitePositiveMass S μD ρD :=
    weightedPowerset_isFinitePositiveMass wD htotal
  refine ⟨I, inferInstance, inferInstance, μD, ρD, hD, i, j, hi, hj,
    fun b => ⟨hiρ b, positiveMass_preserves_mark hB hD i hiρ b⟩,
    fun c => ⟨hjρ c, positiveMass_preserves_mark hC hD j hjρ c⟩,
    fun a => ?_, fun b c heq => ?_⟩
  · ext x
    change x ∈ positiveMassAtomPreimage projL (eB (f a)) ↔
      x ∈ positiveMassAtomPreimage projR (eC (g a))
    rw [hpartB a, hpartC a]
    simpa [positiveMassAtomPreimage, projL, projR] using
      (congrArg (fun z => z ∈ eA a) (hcomm x)).to_iff
  · have hcompat (x : I) : projL x ∈ eB b ↔ projR x ∈ eC c := by
      have h := congrArg (fun u : Finset I => x ∈ u) heq
      simpa [i, j, positiveMassAtomPreimage] using h
    obtain ⟨T, hTB, hTC⟩ := hinter (eB b : Set _) (eC c : Set _) hcompat
    let a : A := eA.symm (Finset.univ.filter fun a => a ∈ T)
    refine ⟨a, eB.injective ?_, eC.injective ?_⟩
    · rw [hpartB a]
      ext z
      change z ∈ positiveMassAtomPreimage partB
        (eA (eA.symm (Finset.univ.filter fun a => a ∈ T))) ↔ z ∈ eB b
      rw [eA.apply_symm_apply]
      simpa [positiveMassAtomPreimage] using (hTB z).symm
    · rw [hpartC a]
      ext z
      change z ∈ positiveMassAtomPreimage partC
        (eA (eA.symm (Finset.univ.filter fun a => a ∈ T))) ↔ z ∈ eC c
      rw [eA.apply_symm_apply]
      simpa [positiveMassAtomPreimage] using (hTC z).symm

end SuccessorTree.NonPrecompact.BooleanBanana
