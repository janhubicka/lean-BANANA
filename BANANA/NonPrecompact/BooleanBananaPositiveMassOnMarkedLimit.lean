import BANANA.NonPrecompact.BooleanBananaPositiveMassConcreteExtension
import BANANA.NonPrecompact.BooleanBananaMassRangeRealisation
import BANANA.NonPrecompact.PrebananaFiniteBridgeGlobalAutomorphism

/-!
# Transport of a positive-mass tower to a fixed marked limit

The weighted cylinders have the finite marked extension property after
forgetting mass. The marked back-and-forth identifies their reduct
with any fixed model satisfying that property. Transporting the weighted
stages along this isomorphism keeps all groups on the fixed carrier.
-/

namespace SuccessorTree.NonPrecompact.BooleanBanana

/-- A concrete positive-mass tower identified with a fixed marked reduct. -/
structure PositiveMassRealisation (M : PrebananaCountableBooleanModel) (S : Set ℕ) where
  tower : PositiveMassDenominatorTower S
  orderIso : tower.Cylinder ≃o M.carrier
  preserves_mark : ∀ x, M.μ (orderIso x) = tower.mark x

namespace PositiveMassRealisation

open MeasureTheory

variable {M : PrebananaCountableBooleanModel} {S : Set ℕ}
  (R : PositiveMassRealisation M S)

/-- Rational mass with total two, on the fixed marked algebra. -/
noncomputable def mass (x : M.carrier) : ℚ := R.tower.mass (R.orderIso.symm x)

/-- Real mass normalised to one, on the same algebra. -/
noncomputable def normalizedMass (x : M.carrier) : ℝ := (R.mass x : ℝ) / 2

/-- The stabiliser of the normalised real mass is exactly the subgroup
preserving the original rational mass. -/
theorem mem_massSubgroup_iff (g : markedAutomorphisms M.μ) :
    g ∈ massSubgroup M.μ R.normalizedMass ↔ ∀ x, R.mass (g.val x) = R.mass x := by
  change (∀ x, (R.mass (g.val x) : ℝ) / 2 = (R.mass x : ℝ) / 2) ↔ _
  constructor
  · intro h x
    have h' := (div_left_inj' (show (2 : ℝ) ≠ 0 by norm_num)).mp (h x)
    exact_mod_cast h'
  · intro h x
    rw [h x]

/-- The coherent uniform tower transported across the reduct isomorphism. -/
noncomputable def uniformTower :
    UniformMassTower R.tower.Label M.μ R.normalizedMass where
  children := R.tower.uniformTower.children
  split := R.tower.uniformTower.split
  stage n := (R.orderIso : BoundedLatticeHom R.tower.Cylinder M.carrier).comp (R.tower.stage n)
  stage_injective n := R.orderIso.injective.comp (R.tower.stage_injective n)
  stage_step n s := congrArg R.orderIso (R.tower.uniformTower.stage_step n s)
  covers x := by
    obtain ⟨n, s, hs⟩ := R.tower.covers (R.orderIso.symm x)
    refine ⟨n, s, (congrArg R.orderIso hs).trans (R.orderIso.apply_symm_apply x)⟩
  mass_stage n s := by
    change (R.tower.mass (R.orderIso.symm (R.orderIso (R.tower.stage n s))) : ℝ) / 2 = _
    rw [R.orderIso.symm_apply_apply]
    exact R.tower.uniformTower.mass_stage n s
  mark_stage n s := (R.preserves_mark _).trans (R.tower.mark_stage n s)

/-- The finite weighted age embeds into this positive-mass realisation. -/
theorem exists_weightedEmbedding
    (A : Type) [BooleanAlgebra A] [Fintype A]
    (μ : A → ZMod 2) (ρ : A → ℚ) (hA : IsFinitePositiveMass S μ ρ) :
    ∃ f : BoundedLatticeHom A M.carrier, Function.Injective f ∧
      (∀ a, M.μ (f a) = μ a) ∧ (∀ a, R.mass (f a) = ρ a) := by
  obtain ⟨e, he, hmark, hmass⟩ := R.tower.exists_weightedEmbedding A μ ρ hA
  refine ⟨(R.orderIso : BoundedLatticeHom R.tower.Cylinder M.carrier).comp e, R.orderIso.injective.comp he,
    fun a => (R.preserves_mark _).trans (hmark a), fun a => ?_⟩
  change R.tower.mass (R.orderIso.symm (R.orderIso (e a))) = ρ a
  rw [R.orderIso.symm_apply_apply, hmass]

/-- Every element of the realisation lies in a finite weighted subalgebra. -/
theorem exists_weightedSubalgebraCover (x : M.carrier) :
    ∃ (A : Type) (_ : BooleanAlgebra A) (_ : Fintype A)
      (f : BoundedLatticeHom A M.carrier) (a : A),
      IsFinitePositiveMass S (M.μ ∘ f) (R.mass ∘ f) ∧ f a = x := by
  obtain ⟨A, hA, hfin, e, a, hweighted, ha⟩ :=
    R.tower.exists_weightedSubalgebraCover (R.orderIso.symm x)
  letI := hA
  letI := hfin
  let f := (R.orderIso : BoundedLatticeHom R.tower.Cylinder M.carrier).comp e
  have hmark : M.μ ∘ f = R.tower.mark ∘ e := funext fun b => R.preserves_mark (e b)
  have hmass : R.mass ∘ f = R.tower.mass ∘ e := by
    funext b
    change R.tower.mass (R.orderIso.symm (R.orderIso (e b))) = R.tower.mass (e b)
    rw [R.orderIso.symm_apply_apply]
  refine ⟨A, hA, hfin, f, a, ?_, (congrArg R.orderIso ha).trans (R.orderIso.apply_symm_apply x)⟩
  rwa [hmark, hmass]

/-- The finite age of the transported tower is contained in the
finite positive-mass class. -/
theorem weightedEmbedding_restrict {A : Type} [BooleanAlgebra A] [Fintype A]
    (e : BoundedLatticeHom A M.carrier) (he : Function.Injective e) :
    IsFinitePositiveMass S (M.μ ∘ e) (R.mass ∘ e) := by
  let e' := (R.orderIso.symm : BoundedLatticeHom M.carrier R.tower.Cylinder).comp e
  have h := R.tower.weightedEmbedding_restrict e' (R.orderIso.symm.injective.comp he)
  have hmark : R.tower.mark ∘ e' = M.μ ∘ e := by
    funext a
    change R.tower.mark (R.orderIso.symm (e a)) = M.μ (e a)
    rw [← R.preserves_mark, R.orderIso.apply_symm_apply]
  rwa [hmark] at h

/-- Every mass-preserving finite partial extension extends into the
realisation on the fixed marked algebra. -/
theorem exists_weightedExtension
    {A C : Type} [BooleanAlgebra A] [Fintype A] [BooleanAlgebra C] [Fintype C]
    {μC : C → ZMod 2} {ρC : C → ℚ} (hC : IsFinitePositiveMass S μC ρC)
    (f : BoundedLatticeHom A C) (hf : Function.Injective f)
    (e : BoundedLatticeHom A M.carrier) (he : Function.Injective e)
    (hρ : ∀ a, ρC (f a) = R.mass (e a)) :
    ∃ j : BoundedLatticeHom C M.carrier, Function.Injective j ∧
      (∀ c, M.μ (j c) = μC c ∧ R.mass (j c) = ρC c) ∧
      ∀ a, j (f a) = e a := by
  let e' := (R.orderIso.symm : BoundedLatticeHom M.carrier R.tower.Cylinder).comp e
  obtain ⟨j, hj, hvalues, hcomm⟩ := R.tower.exists_weightedExtension
    hC f hf e' (R.orderIso.symm.injective.comp he) hρ
  refine ⟨(R.orderIso : BoundedLatticeHom R.tower.Cylinder M.carrier).comp j, R.orderIso.injective.comp hj,
    fun c => ⟨(R.preserves_mark _).trans (hvalues c).1, ?_⟩, fun a => ?_⟩
  · change R.tower.mass (R.orderIso.symm (R.orderIso (j c))) = ρC c
    rw [R.orderIso.symm_apply_apply, (hvalues c).2]
  · change R.orderIso (j (f a)) = e a
    rw [hcomm]
    exact R.orderIso.apply_symm_apply (e a)

/-- The uniform stages give a dense increasing sequence of finite
subgroups of the actual mass-preserving marked automorphism group. -/
theorem massSubgroup_amenable : IsTopologicallyAmenable (massSubgroup M.μ R.normalizedMass) :=
  R.uniformTower.massSubgroup_amenable

local instance stoneMeasurableSpace : MeasurableSpace (BooleanSpectrum.Space M.carrier) :=
  borel _

local instance stoneBorelSpace : BorelSpace (BooleanSpectrum.Space M.carrier) := ⟨rfl⟩

/-- The finite-stage averages give a unique regular invariant probability
on the Stone space, and its clopen values are the prescribed normalised mass. -/
theorem exists_unique_regular_invariantStoneProbability :
    ∃! ν : Measure (BooleanSpectrum.Space M.carrier),
      ν.Regular ∧ IsProbabilityMeasure ν ∧
        (∀ g : massSubgroup M.μ R.normalizedMass, ν.map (fun x => g • x) = ν) ∧
        ∀ b : M.carrier, stoneMass ν b = R.normalizedMass b := by
  let T := R.uniformTower
  obtain ⟨ν, hreg, hprob, hinv⟩ := exists_invariant_probability_of_dense_finite_subgroups
    (X := BooleanSpectrum.Space M.carrier) T.finiteStage
    (fun i j => ⟨max i j, T.finiteStage_mono (le_max_left _ _),
      T.finiteStage_mono (le_max_right _ _)⟩) T.finite_finiteStage T.finiteStage_dense
  letI := hprob
  have hν (g : massSubgroup M.μ R.normalizedMass) : ν.map (fun x => g • x) = ν :=
    (hinv g).map_eq
  refine ⟨ν, ⟨hreg, hprob, hν, stoneMass_eq_of_uniformMassCover T.uniformMassCover ν hν⟩,
    fun μ hμ => ?_⟩
  letI := hμ.2.1
  exact invariantStoneProbability_unique T.uniformMassCover μ ν hμ.2.2.1 hν

/-- The allowed primes are detected by the clopen mass values. -/
theorem prime_mem_iff {p : ℕ} (hp : p.Prime) (hodd : Odd p) :
    p ∈ S ↔ 1 / (2 * (p : ℝ)) ∈ Set.range R.normalizedMass :=
  positiveMass_prime_mem_iff_of_age R.exists_weightedEmbedding R.exists_weightedSubalgebraCover hp hodd

end PositiveMassRealisation

/-- The concrete weighted cylinder tower can be realised on any countable
marked Boolean algebra with the finite ambient and extension properties. -/
theorem nonempty_positiveMassRealisation {M : PrebananaCountableBooleanModel}
    (hfinite : M.HasFiniteAmbients) (hext : M.HasFiniteExtensionProperty)
    {S : Set ℕ} {p : ℕ} (hpS : p ∈ S) (hp : p.Prime) (hodd : Odd p) :
    Nonempty (PositiveMassRealisation M S) := by
  obtain ⟨T⟩ := nonempty_positiveMassDenominatorTower hpS hp hodd
  obtain ⟨E, hmark⟩ := PrebananaCountableBooleanModel.exists_marked_orderIso
    T.reduct_hasFiniteAmbients hfinite (T.reduct_hasFiniteExtensionProperty hpS hp hodd) hext
  exact ⟨⟨T, E, hmark⟩⟩

end SuccessorTree.NonPrecompact.BooleanBanana
