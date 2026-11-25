import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Topology.Algebra.MulAction

/-!
# Invariant probability from a dense directed union of finite subgroups

Finite subgroups admit orbit averages. Weak compactness of probability
measures gives a common solution of their integral invariance equations.
Joint continuity extends the equations to the closure, and regularisation
turns these equations into invariance of the Borel probability measure.
-/

namespace SuccessorTree.NonPrecompact

open MeasureTheory Set
open scoped ENNReal

variable {G X : Type*} [Group G] [TopologicalSpace G]
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [MulAction G X] [ContinuousSMul G X]

omit [T2Space X] in
private theorem continuous_translate_integral (μ : Measure X) [IsProbabilityMeasure μ]
    (f : C(X, ℝ)) : Continuous fun g : G => ∫ x, f (g • x) ∂μ := by
  let translate (g : G) : C(X, ℝ) := ⟨fun x => f (g • x), f.continuous.comp (continuous_const_smul g)⟩
  have htranslate : Continuous translate := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact f.continuous.comp continuous_smul
  let integralMap : C(X, ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun f => ∫ x, f x ∂μ
      map_add' := fun f h => integral_add
        (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f))
        (h.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace h))
      map_smul' := fun c f => integral_smul c f }
  have hbound (f : C(X, ℝ)) : ‖integralMap f‖ ≤ 1 * ‖f‖ := by
    change ‖∫ x, f x ∂μ‖ ≤ 1 * ‖f‖
    simpa using norm_integral_le_of_norm_le_const (μ := μ)
      (Filter.Eventually.of_forall (ContinuousMap.norm_coe_le_norm f))
  exact (integralMap.mkContinuous 1 hbound).continuous.comp htranslate

private noncomputable def subgroupOrbitAverage (K : Subgroup G) [Fintype K]
    (x : X) : ProbabilityMeasure X := by
  classical
  refine ⟨(Fintype.card K : ℝ≥0∞)⁻¹ • ∑ k : K, Measure.dirac ((k : G) • x), ⟨?_⟩⟩
  have hn : Fintype.card K ≠ 0 := Fintype.card_ne_zero
  simpa [Measure.smul_apply, Measure.finsetSum_apply] using
    ENNReal.inv_mul_cancel (a := (Fintype.card K : ℝ≥0∞)) (by exact_mod_cast hn) (by simp)

private theorem subgroupOrbitAverage_invariant (K : Subgroup G) [Fintype K]
    (x : X) (k : K) :
    ((subgroupOrbitAverage K x : ProbabilityMeasure X) : Measure X).map
      (fun y => (k : G) • y) = subgroupOrbitAverage K x := by
  classical
  have hm : Measurable (fun y : X => (k : G) • y) := (continuous_const_smul (k : G)).measurable
  change ((Fintype.card K : ℝ≥0∞)⁻¹ • ∑ j : K, Measure.dirac ((j : G) • x)).map _ = _
  rw [← Measure.mapₗ_apply_of_measurable hm, map_smul, map_sum]
  simp only [Measure.mapₗ_apply_of_measurable hm, Measure.map_dirac' hm]
  change (Fintype.card K : ℝ≥0∞)⁻¹ • ∑ j : K, Measure.dirac ((k : G) • ((j : G) • x)) =
    (Fintype.card K : ℝ≥0∞)⁻¹ • ∑ j : K, Measure.dirac ((j : G) • x)
  congr 1
  calc
    (∑ j : K, Measure.dirac ((k : G) • ((j : G) • x))) =
        ∑ j : K, Measure.dirac (((Equiv.mulLeft k j : K) : G) • x) := by
          apply Finset.sum_congr rfl
          intro j _
          exact congrArg Measure.dirac (mul_smul (k : G) (j : G) x).symm
    _ = ∑ j : K, Measure.dirac ((j : G) • x) :=
      Equiv.sum_comp (Equiv.mulLeft k) (fun j : K => Measure.dirac ((j : G) • x))

/-- The regular probability with the same continuous integrals inherits
all the invariance equations of the original probability. -/
theorem exists_regular_invariant_probability_of_integral_invariant
    (p : ProbabilityMeasure X)
    (hp : ∀ (f : C(X, ℝ)) (g : G),
      (∫ x, f (g • x) ∂(p : Measure X)) = ∫ x, f x ∂(p : Measure X)) :
    ∃ μ : Measure X, Measure.Regular μ ∧ IsProbabilityMeasure μ ∧
      ∀ g : G, MeasurePreserving (fun x : X => g • x) μ μ := by
  obtain ⟨μ, hreg, hfinμ, hμ⟩ := (p : Measure X).exists_regular_eq_of_compactSpace
  have hprob : IsProbabilityMeasure μ := by
    apply isProbabilityMeasure_iff_real.mpr
    simpa using (hμ (BoundedContinuousFunction.const X 1)).symm
  refine ⟨μ, hreg, hprob, fun g => ⟨(continuous_const_smul g).measurable, ?_⟩⟩
  have : (μ.map (fun x : X => g • x)).Regular := by
    have := Measure.InnerRegularCompactLTTop.map_of_continuous
      (continuous_const_smul g) (μ := μ)
    infer_instance
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  change (∫ x, f.toContinuousMap x ∂(μ.map (fun x => g • x))) =
    ∫ x, f.toContinuousMap x ∂μ
  rw [integral_map (continuous_const_smul g).aemeasurable f.continuous.aestronglyMeasurable]
  let q : C(X, ℝ) := f.toContinuousMap
  let t : C(X, ℝ) := ⟨fun x => f (g • x), f.continuous.comp (continuous_const_smul g)⟩
  exact (hμ (BoundedContinuousFunction.mkOfCompact t)).symm.trans
    ((hp q g).trans (hμ (BoundedContinuousFunction.mkOfCompact q)))

/-- Every nonempty compact Hausdorff flow of a group with a dense
directed union of finite subgroups carries an invariant regular
Borel probability measure. -/
theorem exists_invariant_probability_of_dense_finite_subgroups
    [Nonempty X] {ι : Type*} [Nonempty ι] (K : ι → Subgroup G)
    (hK : Directed (· ≤ ·) K) (hfin : ∀ i, Finite (K i))
    (hdense : Dense (⋃ i, (K i : Set G))) :
    ∃ μ : Measure X, Measure.Regular μ ∧ IsProbabilityMeasure μ ∧
      ∀ g : G, MeasurePreserving (fun x : X => g • x) μ μ := by
  classical
  let fixed (i : ι) : Set (ProbabilityMeasure X) :=
    {μ | ∀ (g : K i) (f : C(X, ℝ)),
      (∫ x, f ((g : G) • x) ∂(μ : Measure X)) = ∫ x, f x ∂(μ : Measure X)}
  have hclosed (i) : IsClosed (fixed i) := by
    simp only [fixed, Set.ofPred_forall]
    refine isClosed_iInter fun (g : K i) => isClosed_iInter fun (f : C(X, ℝ)) =>
      isClosed_eq ?_ ?_
    · exact ProbabilityMeasure.continuous_integral_continuousMap
        (⟨fun x => f ((g : G) • x), f.continuous.comp (continuous_const_smul (g : G))⟩ : C(X, ℝ))
    · exact ProbabilityMeasure.continuous_integral_continuousMap f
  have hnonempty (i) : (fixed i).Nonempty := by
    let _ := Fintype.ofFinite (K i)
    obtain ⟨x⟩ := ‹Nonempty X›
    refine ⟨subgroupOrbitAverage (K i) x, fun g f => ?_⟩
    rw [← integral_map (continuous_const_smul (g : G)).aemeasurable
      f.continuous.aestronglyMeasurable, subgroupOrbitAverage_invariant]
  have hdirected : Directed (· ⊇ ·) fixed := by
    intro i j
    obtain ⟨k, hik, hjk⟩ := hK i j
    exact ⟨k, fun μ hμ g f => hμ ⟨g, hik g.property⟩ f,
      fun μ hμ g f => hμ ⟨g, hjk g.property⟩ f⟩
  obtain ⟨p, hp⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    fixed hdirected hnonempty (fun i => (hclosed i).isCompact) hclosed
  have hp' (f : C(X, ℝ)) (g : G) :
      (∫ x, f (g • x) ∂(p : Measure X)) = ∫ x, f x ∂(p : Measure X) := by
    refine hdense.induction ?_ (isClosed_eq (continuous_translate_integral p f) continuous_const) g
    intro h hh
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hh
    exact (Set.mem_iInter.mp hp i) ⟨h, hi⟩ f
  exact exists_regular_invariant_probability_of_integral_invariant p hp'

end SuccessorTree.NonPrecompact
