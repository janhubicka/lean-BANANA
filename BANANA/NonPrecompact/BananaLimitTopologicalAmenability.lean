import BANANA.NonPrecompact.BananaLimitLocallyFiniteDense
import BANANA.NonPrecompact.FiniteSubgroupAmenability
import Mathlib.Data.Set.FiniteExhaustion

/-!
# Topological amenability of the BANANA automorphism group

The topology comes from evaluation at each point of the two discrete
sorts. Finite GL stages are subgroups of this actual group and their
union is dense by the finite-set approximation theorem.
-/

namespace SuccessorTree.NonPrecompact

open Filter Set Topology

/-- The group of simultaneous linear automorphisms preserving the pairing. -/
def bananaLimitAutomorphismGroup : Subgroup BananaLimitLinearPair where
  carrier := {g | ∀ x y : BananaLimitVector,
    bananaLimitPairing (g.1 x) (g.2 y) = bananaLimitPairing x y}
  one_mem' := fun _ _ => rfl
  mul_mem' := fun {f g} hf hg x y => (hf (g.1 x) (g.2 y)).trans (hg x y)
  inv_mem' := fun {g} hg x y => by
    simpa using (hg (g.1.symm x) (g.2.symm y)).symm

/-- Automorphisms of the original two-sorted countable BANANA pairing. -/
abbrev BananaLimitAutomorphism := ↥bananaLimitAutomorphismGroup

/-- A finite GL stage as a subgroup of the full automorphism group. -/
def bananaLimitFiniteGLSubgroup (S : Finset ℚ) : Subgroup BananaLimitAutomorphism where
  carrier := {g | g.val ∈ bananaLimitFiniteGLStage S}
  one_mem' := bananaLimitFiniteGLStage_identity S
  mul_mem' := fun {f g} hf hg =>
    bananaLimitFiniteGLStage_trans S g.val f.val hg hf
  inv_mem' := fun {g} hg => bananaLimitFiniteGLStage_symm S g.val hg

theorem bananaLimitFiniteGLSubgroup_finite (S : Finset ℚ) :
    Finite (bananaLimitFiniteGLSubgroup S) := by
  letI := bananaLimitFiniteGLStage_finite S
  exact Finite.of_injective
    (fun g : bananaLimitFiniteGLSubgroup S => (⟨g.val.val, g.property⟩ :
      {g : BananaLimitLinearPair // g ∈ bananaLimitFiniteGLStage S}))
    (fun _ _ h => by
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun g : {g : BananaLimitLinearPair // g ∈ bananaLimitFiniteGLStage S} =>
        g.val) h)

theorem bananaLimitFiniteGLSubgroup_directed :
    Directed (· ≤ ·) bananaLimitFiniteGLSubgroup := by
  intro S T
  obtain ⟨hS, hT⟩ := bananaLimitFiniteGLStage_directed S T
  exact ⟨S ∪ T, fun _ h => hS h, fun _ h => hT h⟩

private def bananaLimitEvaluation (g : BananaLimitAutomorphism) :
    BananaLimitVector ⊕ BananaLimitVector → BananaLimitVector
  | .inl x => g.val.1 x
  | .inr y => g.val.2 y

local instance : TopologicalSpace BananaLimitVector := ⊥
local instance : DiscreteTopology BananaLimitVector := ⟨rfl⟩

instance : TopologicalSpace BananaLimitAutomorphism :=
  TopologicalSpace.induced bananaLimitEvaluation inferInstance

private theorem continuous_bananaLimitEvaluation (x : BananaLimitVector ⊕ BananaLimitVector) :
    Continuous (fun g : BananaLimitAutomorphism => bananaLimitEvaluation g x) := by
  have h : Continuous bananaLimitEvaluation := continuous_induced_dom
  exact (continuous_apply x).comp h

private theorem continuous_eval_comp
    (side : BananaLimitAutomorphism → BananaLimitVector ≃ₗ[F2] BananaLimitVector)
    (heval : ∀ x, Continuous fun g => side g x) (x : BananaLimitVector) :
    Continuous (fun p : BananaLimitAutomorphism × BananaLimitAutomorphism =>
      side p.1 (side p.2 x)) := by
  have hjoint : Continuous (fun p : BananaLimitAutomorphism × BananaLimitVector =>
      side p.1 p.2) := continuous_prod_of_discrete_right.mpr heval
  exact hjoint.comp (continuous_fst.prodMk ((heval x).comp continuous_snd))

private theorem continuous_eval_symm
    (side : BananaLimitAutomorphism → BananaLimitVector ≃ₗ[F2] BananaLimitVector)
    (heval : ∀ x, Continuous fun g => side g x) (x : BananaLimitVector) :
    Continuous (fun g => (side g).symm x) := by
  rw [continuous_iff_continuousAt]
  intro g
  rw [ContinuousAt, nhds_discrete BananaLimitVector, Filter.tendsto_pure]
  have h := (heval ((side g).symm x)).continuousAt (x := g)
  rw [ContinuousAt, nhds_discrete BananaLimitVector, Filter.tendsto_pure] at h
  filter_upwards [h] with f hf
  apply (side f).injective
  simpa using hf.symm

instance : IsTopologicalGroup BananaLimitAutomorphism where
  continuous_mul := by
    apply continuous_induced_rng.mpr
    apply continuous_pi
    intro i
    cases i with
    | inl x =>
      exact continuous_eval_comp (fun g => g.val.1)
        (fun y => continuous_bananaLimitEvaluation (.inl y)) x
    | inr x =>
      exact continuous_eval_comp (fun g => g.val.2)
        (fun y => continuous_bananaLimitEvaluation (.inr y)) x
  continuous_inv := by
    apply continuous_induced_rng.mpr
    apply continuous_pi
    intro i
    cases i with
    | inl x =>
      exact continuous_eval_symm (fun g => g.val.1)
        (fun y => continuous_bananaLimitEvaluation (.inl y)) x
    | inr x =>
      exact continuous_eval_symm (fun g => g.val.2)
        (fun y => continuous_bananaLimitEvaluation (.inr y)) x

/-- The finite GL stages are dense in the pointwise topology on the
actual automorphism group. -/
theorem bananaLimitFiniteGLSubgroup_dense :
    Dense (⋃ S, (bananaLimitFiniteGLSubgroup S : Set BananaLimitAutomorphism)) := by
  classical
  intro g
  rw [mem_closure_iff_nhds]
  intro U hU
  change U ∈ @nhds _ (TopologicalSpace.induced bananaLimitEvaluation inferInstance) g at hU
  rw [nhds_induced, Filter.mem_comap] at hU
  obtain ⟨V, hV, hVU⟩ := hU
  rw [nhds_pi, Filter.mem_pi'] at hV
  obtain ⟨I, W, hW, hWV⟩ := hV
  let tests := I.image (Sum.elim id id)
  obtain ⟨f, ⟨S, hf⟩, hL, hR⟩ :=
    bananaLimitFiniteGLUnion_pointwise_approximates g.val.1 g.val.2 g.property tests tests
  let f' : BananaLimitAutomorphism := ⟨f,
    bananaLimitFiniteGLUnion_pairing f ⟨S, hf⟩⟩
  refine ⟨f', hVU (hWV ?_), Set.mem_iUnion.mpr ⟨S, hf⟩⟩
  intro i hi
  have hgW := mem_of_mem_nhds (hW i)
  cases i with
  | inl x =>
    have hx : x ∈ tests := Finset.mem_image.mpr ⟨Sum.inl x, hi, rfl⟩
    change f.1 x ∈ W (.inl x)
    rw [hL x hx]
    exact hgW
  | inr y =>
    have hy : y ∈ tests := Finset.mem_image.mpr ⟨Sum.inr y, hi, rfl⟩
    change f.2 y ∈ W (.inr y)
    rw [hR y hy]
    exact hgW

/-- The usual countable exhaustion of the rational coordinates gives
an increasing sequence of finite subgroups with dense union. -/
theorem exists_bananaLimitFiniteGLSequence :
    ∃ K : ℕ → Subgroup BananaLimitAutomorphism, Monotone K ∧
      (∀ n, Finite (K n)) ∧ Dense (⋃ n, (K n : Set BananaLimitAutomorphism)) := by
  classical
  let Q := (Set.to_countable (Set.univ : Set ℚ)).finiteExhaustion
  let S (n : ℕ) := (Q.finite n).toFinset
  have hS : Monotone S := by
    intro m n h x hx
    exact (Q.finite n).mem_toFinset.mpr (Q.mono h ((Q.finite m).mem_toFinset.mp hx))
  have hcofinal (T : Finset ℚ) : ∃ n, T ⊆ S n := by
    induction T using Finset.induction_on with
    | empty => exact ⟨0, Finset.empty_subset _⟩
    | @insert a T ha ih =>
      obtain ⟨m, hm⟩ := ih
      have h : a ∈ ⋃ n, Q n := by simp
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp h
      have han : a ∈ S n := (Q.finite n).mem_toFinset.mpr hn
      refine ⟨max m n, Finset.insert_subset_iff.mpr
        ⟨hS (le_max_right m n) han, hm.trans (hS (le_max_left m n))⟩⟩
  refine ⟨fun n => bananaLimitFiniteGLSubgroup (S n), ?_, ?_, ?_⟩
  · exact fun _ _ h _ hg => bananaLimitFiniteGLStage_mono _ _ (hS h) hg
  · exact fun n => bananaLimitFiniteGLSubgroup_finite (S n)
  · apply bananaLimitFiniteGLSubgroup_dense.mono
    intro g hg
    obtain ⟨T, hT⟩ := Set.mem_iUnion.mp hg
    obtain ⟨n, hn⟩ := hcofinal T
    exact Set.mem_iUnion.mpr ⟨n, bananaLimitFiniteGLStage_mono _ _ hn hT⟩

/-- The countable BANANA pairing's pointwise automorphism group is
amenable: each nonempty compact Hausdorff flow has an invariant regular
Borel probability measure. -/
theorem bananaLimitAutomorphismGroup_amenable (X : Type*) [TopologicalSpace X]
    [T2Space X] [CompactSpace X] [Nonempty X] [MeasurableSpace X] [BorelSpace X]
    [MulAction BananaLimitAutomorphism X] [ContinuousSMul BananaLimitAutomorphism X] :
    ∃ μ : MeasureTheory.Measure X, MeasureTheory.Measure.Regular μ ∧
      MeasureTheory.IsProbabilityMeasure μ ∧
      ∀ g : BananaLimitAutomorphism,
        MeasureTheory.MeasurePreserving (fun x : X => g • x) μ μ :=
  exists_invariant_probability_of_dense_finite_subgroups bananaLimitFiniteGLSubgroup
    bananaLimitFiniteGLSubgroup_directed bananaLimitFiniteGLSubgroup_finite
    bananaLimitFiniteGLSubgroup_dense

end SuccessorTree.NonPrecompact
