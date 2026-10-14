import BANANA.NonPrecompact.PrebananaAmenabilityThreeAtomCopy
import Mathlib.MeasureTheory.Measure.Real

/-!
# From a probability measure on the Stone presentation to finite Boolean mass

A Boolean algebra has a representation by clopen subsets of its Stone
space. Given a bounded-lattice map into measurable subsets of any
probability space, the measure of the represented sets defines a
normalised finitely additive real-valued mass on Boolean elements.

This module formalises that measure-theoretic transfer independently
of the construction of the Stone space or the countable pre-BANANA
Fraïssé limit. The final theorem combines it with the finite
three-atom partition obstruction from the preceding module.

The required group-invariance of the probability measure on the
represented clopen sets is an explicit hypothesis. Continuity of the
group action, amenability and existence of an invariant probability
measure are not claimed here.
-/

namespace SuccessorTree.NonPrecompact

open MeasureTheory

/-- The probability mass induced by a Boolean representation
whose values are measurable subsets of a probability space. -/
noncomputable def prebananaPresentedProbabilityMass
    {β Ω : Type*}
    [BooleanAlgebra β] [MeasurableSpace Ω]
    (ν : Measure Ω)
    (ι : BoundedLatticeHom β (Set Ω)) : β → ℝ :=
  fun x => ν.real (ι x)

/-- The induced mass is finitely additive on disjoint joins. -/
theorem prebananaPresentedProbabilityMass_additive
    {β Ω : Type*}
    [BooleanAlgebra β] [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (ι : BoundedLatticeHom β (Set Ω))
    (hmeas : ∀ x : β, MeasurableSet (ι x))
    (x y : β) (hxy : x ⊓ y = ⊥) :
    prebananaPresentedProbabilityMass ν ι (x ⊔ y) =
      prebananaPresentedProbabilityMass ν ι x +
      prebananaPresentedProbabilityMass ν ι y := by
  have hd : Disjoint (ι x) (ι y) := by
    apply disjoint_iff.mpr
    calc
      ι x ⊓ ι y = ι (x ⊓ y) := (map_inf ι x y).symm
      _ = ι ⊥ := congrArg ι hxy
      _ = ⊥ := map_bot ι
  change ν.real (ι (x ⊔ y)) = ν.real (ι x) + ν.real (ι y)
  rw [map_sup ι x y]
  exact measureReal_union hd (hmeas y)

/-- The induced mass assigns unit mass to the top Boolean element. -/
theorem prebananaPresentedProbabilityMass_top
    {β Ω : Type*}
    [BooleanAlgebra β] [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (ι : BoundedLatticeHom β (Set Ω)) :
    prebananaPresentedProbabilityMass ν ι (⊤ : β) = 1 := by
  change ν.real (ι (⊤ : β)) = 1
  rw [map_top ι]
  exact probReal_univ

/-- An invariant probability mass on the measurable presentation
contradicts the unmarked three-atom partitions whenever the action
is transitive on the proper nonzero zero-marked Boolean elements.

For a Stone space, the hypotheses about the presentation are standard:
each Boolean element denotes a clopen (hence measurable) set, and
a group-invariant probability measure has invariant clopen masses.
-/
theorem prebanana_no_invariantPresentedProbability_of_threeAtom
    {β Ω G : Type*}
    [BooleanAlgebra β] [MeasurableSpace Ω]
    [Group G] [MulAction G β]
    (μ : β → F2)
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (ι : BoundedLatticeHom β (Set Ω))
    (hmeas : ∀ x : β, MeasurableSet (ι x))
    (htrans : ∀ x y : β,
      prebananaProperZeroMark μ x →
      prebananaProperZeroMark μ y →
      ∃ g : G, g • x = y)
    (hinvariant : ∀ g : G, ∀ x : β,
      ν.real (ι (g • x)) = ν.real (ι x))
    (f : BoundedLatticeHom (Finset (Fin 3)) β)
    (hinj : Function.Injective f)
    (hmark : ∀ s : Finset (Fin 3), μ (f s) = 0) :
    False := by
  apply prebanana_no_invariantMass_of_threeAtom_copy
    μ (prebananaPresentedProbabilityMass ν ι)
  · intro x y hxy
    exact prebananaPresentedProbabilityMass_additive ν ι hmeas x y hxy
  · exact prebananaPresentedProbabilityMass_top ν ι
  · exact htrans
  · intro g x
    exact hinvariant g x
  · exact f
  · exact hinj
  · exact hmark

end SuccessorTree.NonPrecompact
