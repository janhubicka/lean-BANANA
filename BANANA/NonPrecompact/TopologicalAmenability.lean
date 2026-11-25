import BANANA.NonPrecompact.FiniteSubgroupAmenability
import Mathlib.Algebra.Group.Action.Hom

/-! The topological amenability property used by the dynamical applications. -/

namespace SuccessorTree.NonPrecompact.BooleanBanana

open MeasureTheory

/-- A topological group is amenable when each of its nonempty compact
Hausdorff flows has an invariant Borel probability measure. -/
def IsTopologicallyAmenable (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
    [MeasurableSpace X] [BorelSpace X] [MulAction G X] [ContinuousSMul G X],
      ∃ ν : Measure X, IsProbabilityMeasure ν ∧ ∀ g : G, ν.map (fun x => g • x) = ν

/-- A dense directed union of finite subgroups is topologically amenable. -/
theorem isTopologicallyAmenable_of_dense_finite_subgroups
    {G : Type*} [Group G] [TopologicalSpace G] {ι : Type*} [Nonempty ι]
    (K : ι → Subgroup G) (hK : Directed (· ≤ ·) K) (hfin : ∀ i, Finite (K i))
    (hdense : Dense (⋃ i, (K i : Set G))) : IsTopologicallyAmenable G := by
  intro X _ _ _ _ _ _ _ _
  obtain ⟨μ, _, hprob, hinv⟩ :=
    exists_invariant_probability_of_dense_finite_subgroups (X := X) K hK hfin hdense
  exact ⟨μ, hprob, fun g => (hinv g).map_eq⟩

/-- Amenability passes through continuous surjective group homomorphisms
by pulling a compact action back along the homomorphism. -/
theorem amenability_of_continuousSurjectiveHom {G H : Type} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H] (f : G →* H) (hc : Continuous f)
    (hs : Function.Surjective f) (hA : IsTopologicallyAmenable G) :
    IsTopologicallyAmenable H := by
  intro X _ _ _ _ _ _ _ _
  letI : MulAction G X := MulAction.compHom X f
  letI : ContinuousSMul G X := ⟨
    (show Continuous (fun p : H × X => p.1 • p.2) from continuous_smul).comp
      ((hc.comp continuous_fst).prodMk continuous_snd)⟩
  obtain ⟨ν, hν, hinv⟩ := hA X
  refine ⟨ν, hν, ?_⟩
  intro h
  obtain ⟨g, rfl⟩ := hs h
  exact hinv g

end SuccessorTree.NonPrecompact.BooleanBanana
