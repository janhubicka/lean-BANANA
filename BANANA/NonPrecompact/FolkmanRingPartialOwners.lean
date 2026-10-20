import BANANA.NonPrecompact.FolkmanPartialAtomOwners

/-!
# From the actual Boolean-ring language to partial atom owners

The Folkman circulation language uses symmetric difference, intersection
and the zero element, but does not name a greatest element.  This module
closes the finite-powerset ring-language interface: preservation of
symmetric difference and intersection already implies preservation of
union.  Consequently the exact partial atom-owner theorem applies.

The source and target atom sets may be empty (the one-element zero ring).
No preservation of the greatest element is assumed or concluded.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical

/-- In a finite powerset Boolean ring, union is definable using
symmetric difference and intersection.  The identity is valid for
empty atom sets as well as nonempty ones. -/
theorem folkmanFinset_union_eq_symmDiff_symmDiff_inter
    {α : Type*} [DecidableEq α] (s t : Finset α) :
    s ∪ t = symmDiff (symmDiff s t) (s ∩ t) := by
  classical
  ext a
  simp only [Finset.mem_union, Finset.mem_symmDiff, Finset.mem_inter]
  tauto

/-- A finite powerset map preserving the two operations of the
Boolean-ring language also preserves (unnamed) union. -/
theorem folkmanPowersetMap_union_of_ringOperations
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (F : Finset ι → Finset κ)
    (hxor : ∀ s t : Finset ι,
      F (symmDiff s t) = symmDiff (F s) (F t))
    (hinter : ∀ s t : Finset ι,
      F (s ∩ t) = F s ∩ F t)
    (s t : Finset ι) :
    F (s ∪ t) = F s ∪ F t := by
  calc
    F (s ∪ t) =
      F (symmDiff (symmDiff s t) (s ∩ t)) := by
        rw [folkmanFinset_union_eq_symmDiff_symmDiff_inter]
    _ = symmDiff (F (symmDiff s t)) (F (s ∩ t)) := hxor _ _
    _ = symmDiff (symmDiff (F s) (F t)) (F s ∩ F t) := by
      rw [hxor, hinter]
    _ = F s ∪ F t :=
      (folkmanFinset_union_eq_symmDiff_symmDiff_inter (F s) (F t)).symm

/-- Exact partial-owner representation for every injective
non-unital finite Boolean-ring embedding in its actual language:
zero, symmetric difference, intersection.  No top preservation. -/
theorem folkman_exists_partialOwner_of_ringEmbedding
    {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (F : Finset ι → Finset κ)
    (hzero : F ∅ = ∅)
    (hxor : ∀ s t : Finset ι,
      F (symmDiff s t) = symmDiff (F s) (F t))
    (hinter : ∀ s t : Finset ι,
      F (s ∩ t) = F s ∩ F t)
    (hinj : Function.Injective F) :
    ∃ part : κ → Option ι,
      (∀ i : ι, ∃ b : κ, part b = some i) ∧
      (∀ s : Finset ι,
        F s = Finset.univ.filter
          (fun b => ∃ i ∈ s, part b = some i)) := by
  classical
  exact folkman_exists_partialOwner_of_powersetEmbedding
    F hzero (folkmanPowersetMap_union_of_ringOperations F hxor hinter)
    hinter hinj

end SuccessorTree.NonPrecompact
