import BANANA.NonPrecompact.FolkmanRingPartialOwners
import Mathlib.Algebra.Ring.BooleanRing

/-!
# Canonical finite atom coordinates for native Boolean rings

The strong-amalgamation construction is already kernel-checked on
finite powerset rings, including empty atom sets.  This file provides
the reusable *object-level* bridge from Mathlib's native BooleanRing
to finite atom coordinates.

For a finite Boolean ring α, the Boolean algebra AsBoolAlg α has the
same underlying carrier, and its canonical atom representation gives
an equivalence with finite subsets of atoms.  Both source and target
objects are coded separately, so no embedding is assumed to preserve
the greatest element.

These lemmas concern ring operations on each whole finite object.
The final transport of arbitrary injective non-unital ring maps,
their compatible bilinear pairings and strong amalgamation is a
separate theorem.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical symmDiff

/-- The canonical finite atom code of a native finite Boolean ring.
The zero ring is permitted: its atom type is empty. -/
noncomputable def folkmanNativeRingAtomEquiv
    (α : Type*) [BooleanRing α] [Fintype α] :
    α ≃ Finset (PrebananaAbstractAtoms (AsBoolAlg α)) := by
  classical
  letI : Fintype (AsBoolAlg α) := Fintype.ofEquiv α toBoolAlg
  exact (toBoolAlg : α ≃ AsBoolAlg α).trans
    (prebananaFiniteBooleanAtomFinsetOrderIso (AsBoolAlg α)).toEquiv

/-- The canonical atom code is injective for every finite Boolean ring. -/
theorem folkmanNativeRingAtomEquiv_injective
    (α : Type*) [BooleanRing α] [Fintype α] :
    Function.Injective (folkmanNativeRingAtomEquiv α) :=
  (folkmanNativeRingAtomEquiv α).injective

/-- The canonical atom code is surjective even for the zero ring. -/
theorem folkmanNativeRingAtomEquiv_surjective
    (α : Type*) [BooleanRing α] [Fintype α] :
    Function.Surjective (folkmanNativeRingAtomEquiv α) :=
  (folkmanNativeRingAtomEquiv α).surjective

/-- Native ring zero is represented by the empty set of atoms. -/
theorem folkmanNativeRingAtomEquiv_zero
    (α : Type*) [BooleanRing α] [Fintype α] :
    folkmanNativeRingAtomEquiv α (0 : α) = ∅ := by
  classical
  letI : Fintype (AsBoolAlg α) := Fintype.ofEquiv α toBoolAlg
  let e := prebananaFiniteBooleanAtomFinsetOrderIso (AsBoolAlg α)
  change e (toBoolAlg (0 : α)) = ∅
  simpa only [toBoolAlg_zero] using e.map_bot

/-- Native ring multiplication becomes intersection of atom sets. -/
theorem folkmanNativeRingAtomEquiv_mul
    (α : Type*) [BooleanRing α] [Fintype α]
    (x y : α) :
    folkmanNativeRingAtomEquiv α (x * y) =
      folkmanNativeRingAtomEquiv α x ∩
        folkmanNativeRingAtomEquiv α y := by
  classical
  letI : Fintype (AsBoolAlg α) := Fintype.ofEquiv α toBoolAlg
  let e := prebananaFiniteBooleanAtomFinsetOrderIso (AsBoolAlg α)
  change e (toBoolAlg (x * y)) =
    e (toBoolAlg x) ∩ e (toBoolAlg y)
  simpa only [toBoolAlg_mul] using e.map_inf (toBoolAlg x) (toBoolAlg y)

/-- Native ring addition becomes symmetric difference of atom sets.
This is the crucial non-unital ring-language coordinate identity. -/
theorem folkmanNativeRingAtomEquiv_add
    (α : Type*) [BooleanRing α] [Fintype α]
    (x y : α) :
    folkmanNativeRingAtomEquiv α (x + y) =
      symmDiff (folkmanNativeRingAtomEquiv α x)
        (folkmanNativeRingAtomEquiv α y) := by
  classical
  letI : Fintype (AsBoolAlg α) := Fintype.ofEquiv α toBoolAlg
  let e := prebananaFiniteBooleanAtomFinsetOrderIso (AsBoolAlg α)
  change e (toBoolAlg (x + y)) =
    symmDiff (e (toBoolAlg x)) (e (toBoolAlg y))
  simpa only [toBoolAlg_add] using
    (map_symmDiff' e (toBoolAlg x) (toBoolAlg y))

end SuccessorTree.NonPrecompact
