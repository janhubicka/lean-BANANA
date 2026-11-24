import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Baire.LocallyCompactRegular

/-!
# Baire-category step in the pre-BANANA charge-space argument

The proof in the manuscript covers an orbit by countably many closed
evaluation fibres and proves that each fibre has empty interior. The
lemmas here perform the ensuing Baire-category argument. Constructing
the evaluation map and proving the orbit-containment and perturbation
hypotheses are separate steps.
-/

open Set

namespace SuccessorTree.NonPrecompact

/-- A set whose evaluation values belong to a countable set of closed
fibres with empty interior is meagre. -/
theorem isMeagre_of_countable_closed_evaluation_fibres
    {X Y : Type*} [TopologicalSpace X] {eval : X → Y}
    {s : Set X} {values : Set Y} (hvalues : values.Countable)
    (hs : s ⊆ eval ⁻¹' values)
    (hclosed : ∀ y ∈ values, IsClosed (eval ⁻¹' {y}))
    (hinterior : ∀ y ∈ values, interior (eval ⁻¹' {y}) = ∅) :
    IsMeagre s := by
  have hmeagre : IsMeagre (⋃ y ∈ values, eval ⁻¹' {y}) :=
    isMeagre_biUnion hvalues fun y hy =>
      ((hclosed y hy).isNowhereDense_iff.mpr (hinterior y hy)).isMeagre
  apply hmeagre.mono
  intro x hx
  exact mem_iUnion.mpr ⟨eval x, mem_iUnion.mpr ⟨hs hx, mem_singleton (eval x)⟩⟩

/-- In a nonempty compact Hausdorff space, an orbit contained in the
evaluation fibres indexed by a countable range is meagre and is not
comeagre if these fibres have empty interior. Continuity makes the
fibres closed. The orbit enters solely through its set of points. -/
theorem isMeagre_and_not_mem_residual_of_countable_evaluation_range
    {X Y A : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
    [TopologicalSpace Y] [T1Space Y] [Countable A] {eval : X → Y}
    (values : A → Y) {s : Set X} (heval : Continuous eval)
    (hs : s ⊆ eval ⁻¹' range values)
    (hinterior : ∀ y ∈ range values, interior (eval ⁻¹' {y}) = ∅) :
    IsMeagre s ∧ s ∉ residual X := by
  have hmeagre := isMeagre_of_countable_closed_evaluation_fibres
    (countable_range values) hs (fun _ _ => isClosed_singleton.preimage heval) hinterior
  exact ⟨hmeagre, fun h => not_isMeagre_of_mem_residual h hmeagre⟩

end SuccessorTree.NonPrecompact
