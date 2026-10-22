import BANANA.NonPrecompact.FolkmanNativeRingAtomEquiv

/-!
# Inverse finite-atom coordinates of a native Boolean ring

The canonical atom equivalence is already shown to send native ring
addition to symmetric difference and multiplication to intersection.
The inverse identities below eliminate repeated coordinate transports
when transferring the six objects and three pairings of a Folkman
amalgamation diagram. In particular, zero rings remain permitted.

This module uses an equivalence of finite carriers and does not require
a non-unital embedding to preserve the greatest element.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical symmDiff

/-- Reading the empty atom set back into a native ring gives its zero. -/
theorem folkmanNativeRingAtomEquiv_symm_empty
    (α : Type*) [BooleanRing α] [Fintype α] :
    (folkmanNativeRingAtomEquiv α).symm ∅ = 0 := by
  classical
  let e := folkmanNativeRingAtomEquiv α
  apply e.injective
  change e (e.symm ∅) = e (0 : α)
  rw [e.apply_symm_apply, folkmanNativeRingAtomEquiv_zero]

/-- Addition of the native ring is symmetric difference on its atom code,
also in the inverse direction. -/
theorem folkmanNativeRingAtomEquiv_symm_symmDiff
    (α : Type*) [BooleanRing α] [Fintype α]
    (s t : Finset (PrebananaAbstractAtoms (AsBoolAlg α))) :
    (folkmanNativeRingAtomEquiv α).symm (symmDiff s t) =
      (folkmanNativeRingAtomEquiv α).symm s +
      (folkmanNativeRingAtomEquiv α).symm t := by
  classical
  let e := folkmanNativeRingAtomEquiv α
  apply e.injective
  change e (e.symm (symmDiff s t)) = e (e.symm s + e.symm t)
  rw [e.apply_symm_apply, folkmanNativeRingAtomEquiv_add]
  simp [e]

/-- Multiplication of a native Boolean ring is intersection of atom
supports also after transport back to its underlying carrier. -/
theorem folkmanNativeRingAtomEquiv_symm_inter
    (α : Type*) [BooleanRing α] [Fintype α]
    (s t : Finset (PrebananaAbstractAtoms (AsBoolAlg α))) :
    (folkmanNativeRingAtomEquiv α).symm (s ∩ t) =
      (folkmanNativeRingAtomEquiv α).symm s *
      (folkmanNativeRingAtomEquiv α).symm t := by
  classical
  let e := folkmanNativeRingAtomEquiv α
  apply e.injective
  change e (e.symm (s ∩ t)) = e (e.symm s * e.symm t)
  rw [e.apply_symm_apply, folkmanNativeRingAtomEquiv_mul]
  simp [e]

end SuccessorTree.NonPrecompact
