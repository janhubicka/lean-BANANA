import BANANA.NonPrecompact.BooleanBananaStoneAction
import BANANA.NonPrecompact.BooleanInvariantMass
import BANANA.NonPrecompact.TopologicalAmenability

/-!
# The three-atom nonamenability obstruction for Boolean actions

A subgroup of the Boolean automorphism group which is transitive on all
proper nonzero elements admits no invariant Stone probability if a
three-atom subalgebra exists.
-/

namespace SuccessorTree.NonPrecompact.BooleanBanana

open MeasureTheory

variable {B : Type} [BooleanAlgebra B] [Nontrivial B]

local instance obstructionMeasurableSpace : MeasurableSpace (BooleanSpectrum.Space B) := borel _
local instance obstructionBorelSpace : BorelSpace (BooleanSpectrum.Space B) := ⟨rfl⟩

/-- A subgroup acting transitively on the proper nonzero Boolean
elements is not amenable if there is a three-atom subalgebra. -/
theorem not_amenable_of_transitiveBooleanSubgroup
    (H : Subgroup (markedAutomorphisms (fun _ : B => ())))
    (htrans : ∀ x y : B, x ≠ ⊥ → x ≠ ⊤ → y ≠ ⊥ → y ≠ ⊤ →
      ∃ g : H, g.val.val x = y)
    (f : BoundedLatticeHom (Finset (Fin 3)) B) (hfinj : Function.Injective f) :
    ¬ IsTopologicallyAmenable H := by
  classical
  intro hAmen
  obtain ⟨ν, hν, hinv⟩ := hAmen (BooleanSpectrum.Space B)
  letI := hν
  let ι : BoundedLatticeHom B (Set (BooleanSpectrum.Space B)) := BooleanSpectrum.toSets
  have hmeas (x : B) : MeasurableSet (ι x) := (BooleanSpectrum.clopens x).isOpen.measurableSet
  have hmass (g : H) (x : B) : ν.real (ι (g.val.val x)) = ν.real (ι x) := by
    have hmeasAction := (continuous_const_smul (g⁻¹ : H) :
      Continuous (fun p : BooleanSpectrum.Space B => (g⁻¹ : H) • p)).measurable
    have hmap := congrArg (fun m : Measure (BooleanSpectrum.Space B) => m (ι x)) (hinv g⁻¹)
    change (ν.map (fun p : BooleanSpectrum.Space B => (g.val⁻¹) • p)) (ι x) = ν (ι x) at hmap
    change Measurable (fun p : BooleanSpectrum.Space B => (g.val⁻¹) • p) at hmeasAction
    rw [Measure.map_apply hmeasAction (hmeas x)] at hmap
    change ν ((fun p : BooleanSpectrum.Space B => (g.val⁻¹) • p) ⁻¹'
      (BooleanSpectrum.clopens x : Set (BooleanSpectrum.Space B))) = ν (ι x) at hmap
    rw [stoneAction_preimage_clopens] at hmap
    exact congrArg ENNReal.toReal hmap
  have hequal (x y : B) (hx : prebananaProperZeroMark (fun _ : B => 0) x)
      (hy : prebananaProperZeroMark (fun _ : B => 0) y) :
      prebananaPresentedProbabilityMass ν ι x = prebananaPresentedProbabilityMass ν ι y := by
    obtain ⟨g, hg⟩ := htrans x y hx.1 hx.2.1 hy.1 hy.2.1
    change ν.real (ι x) = ν.real (ι y)
    exact (hmass g x).symm.trans (congrArg (fun z => ν.real (ι z)) hg)
  exact prebanana_no_uniformMass_of_threeAtom_copy (fun _ : B => 0)
    (prebananaPresentedProbabilityMass ν ι)
    (prebananaPresentedProbabilityMass_additive ν ι hmeas)
    (prebananaPresentedProbabilityMass_top ν ι)
    hequal f hfinj (fun _ => rfl)

/-- Continuous actions through Boolean automorphisms give the same
obstruction for the acting group, by its continuous map onto the image. -/
theorem not_amenable_of_transitiveBooleanHom {G : Type} [Group G] [TopologicalSpace G]
    (ρ : G →* markedAutomorphisms (fun _ : B => ())) (hρ : Continuous ρ)
    (htrans : ∀ x y : B, x ≠ ⊥ → x ≠ ⊤ → y ≠ ⊥ → y ≠ ⊤ →
      ∃ g : G, (ρ g).val x = y)
    (f : BoundedLatticeHom (Finset (Fin 3)) B) (hfinj : Function.Injective f) :
    ¬ IsTopologicallyAmenable G := by
  intro hAmen
  let h := ρ.rangeRestrict
  have hc : Continuous h := hρ.subtype_mk _
  have hs : Function.Surjective h := fun g => by
    obtain ⟨x, hx⟩ := g.property
    exact ⟨x, Subtype.ext hx⟩
  apply not_amenable_of_transitiveBooleanSubgroup ρ.range ?_ f hfinj
    (amenability_of_continuousSurjectiveHom h hc hs hAmen)
  intro x y hx0 hx1 hy0 hy1
  obtain ⟨g, hg⟩ := htrans x y hx0 hx1 hy0 hy1
  exact ⟨h g, hg⟩

end SuccessorTree.NonPrecompact.BooleanBanana
