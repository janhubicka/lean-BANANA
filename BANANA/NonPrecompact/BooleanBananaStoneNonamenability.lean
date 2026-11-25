import BANANA.NonPrecompact.TopologicalAmenability
import BANANA.NonPrecompact.BooleanBananaStoneAction
import BANANA.NonPrecompact.PrebananaActualGeneratedBooleanOps
import BANANA.NonPrecompact.PrebananaFiveAryCylinderFiniteAge
import BANANA.NonPrecompact.PrebananaFiveAryCylinderUltrahomogeneity
import BANANA.NonPrecompact.PrebananaStoneMeasureMass
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.Map

/-!
# Nonamenability of the Boolean–BANANA limit

The Stone action of the actual marked cylinder automorphism group has no
invariant Borel probability measure. Homogeneity puts all proper nonzero
zero-marked elements in one orbit. An embedded unmarked three-atom model
partitions the top into both two and three such elements, so their common
clopen mass would satisfy both normalisation equations.
-/

namespace SuccessorTree.NonPrecompact.BooleanBanana

open MeasureTheory

/-- The full marking-preserving automorphism group of the explicit limit,
with the topology of pointwise convergence. -/
noncomputable abbrev LimitAutomorphisms := markedAutomorphisms prebananaFiveAryCylinderMark

/-- A Stone space of the Boolean–BANANA limit. -/
abbrev LimitStoneSpace := BooleanSpectrum.Space PrebananaFiveAryCylinderLimitCarrier

noncomputable local instance : MeasurableSpace LimitStoneSpace := borel LimitStoneSpace

local instance : BorelSpace LimitStoneSpace := ⟨rfl⟩

private theorem properZeroMark_transitive
    (x y : PrebananaFiveAryCylinderLimitCarrier)
    (hx : prebananaProperZeroMark prebananaFiveAryCylinderMark x)
    (hy : prebananaProperZeroMark prebananaFiveAryCylinderMark y) :
    ∃ g : LimitAutomorphisms, g • x = y := by
  classical
  let S := prebananaGeneratedBooleanSubalgebra PrebananaFiveAryCylinderLimitCarrier
    (fun _ : Fin 1 => x)
  let U := prebananaGeneratedBooleanSubalgebra PrebananaFiveAryCylinderLimitCarrier
    (fun _ : Fin 1 => y)
  letI : Fintype S := @Fintype.ofFinite S (prebananaOneGeneratorFinite x)
  letI : Fintype U := @Fintype.ofFinite U (prebananaOneGeneratorFinite y)
  let A := prebananaCylinder_finiteSubmodel S
  let C := prebananaCylinder_finiteSubmodel U
  let e := prebananaOneGeneratorMarkedIso
    prebananaFiveAryCylinderMark prebananaFiveAryCylinderMark
    prebananaFiveAryCylinderMark_bot prebananaFiveAryCylinderMark_top
    prebananaFiveAryCylinderMark_sup prebananaFiveAryCylinderMark_bot
    prebananaFiveAryCylinderMark_top prebananaFiveAryCylinderMark_sup x y hx hy
  let f : PrebananaFiniteBooleanEmbedding A C := {
    hom := {
      toFun := e.toGeneratedEquiv
      map_bot' := e.toGeneratedEquiv_map_bot
      map_top' := e.toGeneratedEquiv_map_top
      map_sup' := e.toGeneratedEquiv_map_sup
      map_inf' := e.toGeneratedEquiv_map_inf }
    injective := e.toGeneratedEquiv.injective
    preserves_μ := e.toGeneratedEquiv_preserves_mark }
  obtain ⟨g, hmark, hg⟩ := prebananaCylinder_exists_global_marked_boolean_automorphism
    A (prebananaCylinder_finiteSubmodel_embedding S)
    ((prebananaCylinder_finiteSubmodel_embedding U).comp f)
  let a : A.carrier := ⟨x, BooleanSubalgebra.subset_closure ⟨0, rfl⟩⟩
  refine ⟨ofMarkedOrderIso g hmark, ?_⟩
  change g x = y
  exact (hg a).trans (e.toGeneratedEquiv_map_term (.generator 0))

/-- The continuous Stone action of the Boolean–BANANA automorphism group
has no invariant Borel probability measure. -/
theorem no_invariantStoneProbability
    (ν : Measure LimitStoneSpace) [IsProbabilityMeasure ν]
    (hinvariant : ∀ g : LimitAutomorphisms, ν.map (fun x => g • x) = ν) :
    False := by
  let ι : BoundedLatticeHom PrebananaFiveAryCylinderLimitCarrier (Set LimitStoneSpace) :=
    BooleanSpectrum.toSets
  have hmeas (x : PrebananaFiveAryCylinderLimitCarrier) : MeasurableSet (ι x) :=
    (BooleanSpectrum.clopens x).isOpen.measurableSet
  have hmass (g : LimitAutomorphisms) (x : PrebananaFiveAryCylinderLimitCarrier) :
      ν.real (ι (g • x)) = ν.real (ι x) := by
    have hmeasAction : Measurable (fun p : LimitStoneSpace => g⁻¹ • p) :=
      (BooleanSpectrum.homeomorph (g⁻¹ : LimitAutomorphisms).val).continuous.measurable
    have hmap := congrArg (fun m : Measure LimitStoneSpace => m (ι x)) (hinvariant g⁻¹)
    change (ν.map (fun p : LimitStoneSpace => g⁻¹ • p)) (ι x) = ν (ι x) at hmap
    rw [Measure.map_apply hmeasAction (hmeas x)] at hmap
    change ν ((fun p : LimitStoneSpace => g⁻¹ • p) ⁻¹'
      (BooleanSpectrum.clopens x : Set LimitStoneSpace)) = ν (ι x) at hmap
    rw [stoneAction_preimage_clopens] at hmap
    exact congrArg ENNReal.toReal hmap
  obtain ⟨f⟩ := prebananaCylinder_allFiniteModels_embed prebananaThreeAtomAbstractModel
  exact prebanana_no_invariantPresentedProbability_of_threeAtom
    (G := LimitAutomorphisms) prebananaFiveAryCylinderMark ν ι hmeas
    properZeroMark_transitive hmass f.hom f.injective f.preserves_μ

/-- The automorphism group of the concrete Boolean–BANANA limit with the
pointwise topology is not amenable. -/
theorem limit_not_amenable : ¬ IsTopologicallyAmenable LimitAutomorphisms := by
  intro h
  obtain ⟨ν, hprob, hinv⟩ := h LimitStoneSpace
  letI := hprob
  exact no_invariantStoneProbability ν hinv

end SuccessorTree.NonPrecompact.BooleanBanana
