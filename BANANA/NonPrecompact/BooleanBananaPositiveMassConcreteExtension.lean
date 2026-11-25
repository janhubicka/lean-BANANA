import BANANA.NonPrecompact.BooleanBananaPositiveMassConcreteTower
import BANANA.NonPrecompact.BooleanBananaPositiveMassReasonable
import BANANA.NonPrecompact.PrebananaCountableOnePointExtension

/-!
# Finite extensions of the positive-mass cylinder tower

Finite embeddings factor through one uniform stage. Reasonability lifts
a marked extension by assigning a compatible mass to its larger algebra,
and cofinality of the uniform denominators embeds that weighted extension
over the prescribed smaller structure.
-/

namespace SuccessorTree.NonPrecompact.BooleanBanana.PositiveMassDenominatorTower

variable {S : Set ℕ} (T : PositiveMassDenominatorTower S)

/-- The marked reduct of the countable positive-mass cylinder algebra. -/
noncomputable def markedReduct : PrebananaCountableBooleanModel where
  carrier := T.Cylinder
  μ := T.mark
  μ_bot := T.mark_bot
  μ_top := T.mark_top
  μ_add := fun _ _ h => T.mark_add h

/-- Finite sets of the reduct are contained in genuine finite subalgebras. -/
theorem reduct_hasFiniteAmbients : T.markedReduct.HasFiniteAmbients := by
  classical
  intro xs
  obtain ⟨n, hn⟩ := T.exists_finiteAmbient xs
  let A := (⊤ : BooleanSubalgebra (Finset (T.Label n))).map (T.stage n)
  refine ⟨A, ?_, ?_⟩
  · have heq : (A : Set T.Cylinder) = Set.range (T.stage n) := by
      change (T.stage n) '' (⊤ : BooleanSubalgebra (Finset (T.Label n))) = _
      rw [BooleanSubalgebra.coe_top, Set.image_univ]
    exact Set.finite_coe_iff.mp (heq.symm ▸ Set.finite_range (T.stage n))
  · intro x hx
    obtain ⟨s, hs⟩ := hn x hx
    exact ⟨s, BooleanSubalgebra.mem_top, hs⟩

/-- Every finite positive-mass model embeds into the concrete tower. -/
theorem exists_weightedEmbedding
    (A : Type) [BooleanAlgebra A] [Fintype A]
    (μ : A → ZMod 2) (ρ : A → ℚ) (hA : IsFinitePositiveMass S μ ρ) :
    ∃ f : BoundedLatticeHom A T.Cylinder, Function.Injective f ∧
      (∀ a, T.mark (f a) = μ a) ∧ (∀ a, T.mass (f a) = ρ a) := by
  obtain ⟨d, hd, hemb⟩ := exists_positiveMass_uniformStageEmbedding hA
  obtain ⟨n, hdn⟩ := T.cofinal d hd
  obtain ⟨e, he, hpres⟩ := hemb (T.Label n) (T.D n) (T.allowed n) hdn (T.stage_card n)
  refine ⟨(T.stage n).comp e, (T.stage_injective n).comp he, fun a => ?_, fun a => ?_⟩
  · exact (T.mark_stage n (e a)).trans (hpres a).2
  · exact (T.mass_stage n (e a)).trans (hpres a).1

/-- Every tower element belongs to a finite weighted stage. -/
theorem exists_weightedSubalgebraCover (x : T.Cylinder) :
    ∃ (A : Type) (_ : BooleanAlgebra A) (_ : Fintype A)
      (f : BoundedLatticeHom A T.Cylinder) (a : A),
      IsFinitePositiveMass S (T.mark ∘ f) (T.mass ∘ f) ∧ f a = x := by
  obtain ⟨n, s, hs⟩ := T.covers x
  exact ⟨Finset (T.Label n), inferInstance, inferInstance, T.stage n, s,
    T.stage_weighted n, hs⟩

/-- Pulling the tower marking and mass back along a finite embedding
gives a member of the finite positive-mass class. -/
theorem weightedEmbedding_restrict {A : Type} [BooleanAlgebra A] [Fintype A]
    (e : BoundedLatticeHom A T.Cylinder) (he : Function.Injective e) :
    IsFinitePositiveMass S (T.mark ∘ e) (T.mass ∘ e) := by
  obtain ⟨m, g, hg, hge⟩ := T.exists_stageFactor e he
  have h := positiveMass_restrict (T.stage_weighted m) g hg
  have heq : (T.stage m : Finset (T.Label m) → T.Cylinder) ∘ g = e := funext hge
  simpa only [Function.comp_assoc, heq] using h

/-- Arbitrary previously embedded finite positive-mass structures extend
along finite positive-mass embeddings into the concrete tower. -/
theorem exists_weightedExtension
    {A C : Type} [BooleanAlgebra A] [Fintype A] [BooleanAlgebra C] [Fintype C]
    {μC : C → ZMod 2} {ρC : C → ℚ} (hC : IsFinitePositiveMass S μC ρC)
    (f : BoundedLatticeHom A C) (hf : Function.Injective f)
    (e : BoundedLatticeHom A T.Cylinder) (he : Function.Injective e)
    (hρ : ∀ a, ρC (f a) = T.mass (e a)) :
    ∃ j : BoundedLatticeHom C T.Cylinder, Function.Injective j ∧
      (∀ c, T.mark (j c) = μC c ∧ T.mass (j c) = ρC c) ∧
      ∀ a, j (f a) = e a := by
  obtain ⟨m, g, hg, hge⟩ := T.exists_stageFactor e he
  have hpres (a : A) : ρC (f a) = ((g a).card : ℚ) / (T.D m : ℚ) := by
    rw [hρ, ← hge a, T.mass_stage]
  obtain ⟨n, hmn, k, hk, hvalues, hcomm⟩ := positiveMass_uniformTower_extension
    T.D T.allowed (fun _ _ h => T.denominator_dvd h) T.cofinal T.Label T.stage_card
    T.lift T.lift_injective (fun _ _ h s => T.lift_mass h s) hC m f hf g hg hpres
  refine ⟨(T.stage n).comp k, (T.stage_injective n).comp hk, fun c => ?_, fun a => ?_⟩
  · exact ⟨(T.mark_stage n (k c)).trans (hvalues c).2,
      (T.mass_stage n (k c)).trans (hvalues c).1⟩
  · change T.stage n (k (f a)) = e a
    rw [hcomm, T.stage_lift hmn, hge]

/-- Reasonability and the genuine weighted extension property identify
the reduct as a countable marked model with the finite extension property. -/
theorem reduct_hasFiniteExtensionProperty {p : ℕ}
    (hpS : p ∈ S) (hp : p.Prime) (hodd : Odd p) :
    T.markedReduct.HasFiniteExtensionProperty := by
  intro A C f e
  have hA : IsFinitePositiveMass S A.μ (T.mass ∘ e.hom) := by
    have hmark : (T.mark ∘ e.hom : A.carrier → ZMod 2) = A.μ :=
      funext e.preserves_μ
    exact hmark ▸ T.weightedEmbedding_restrict e.hom e.injective
  obtain ⟨ρ, hC, hρ⟩ := positiveMass_reasonable hpS hp hodd hA C.μ C.μ_bot C.μ_add
    f.hom f.injective f.preserves_μ
  obtain ⟨j, hj, hm, heq⟩ := T.exists_weightedExtension hC f.hom f.injective
    e.hom e.injective hρ
  exact ⟨⟨j, hj, fun c => (hm c).1⟩, heq⟩

end SuccessorTree.NonPrecompact.BooleanBanana.PositiveMassDenominatorTower
