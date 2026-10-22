import BANANA.NonPrecompact.FolkmanNativeRingMapCoordinates

/-!
# Transporting native bilinear Folkman pairings to atom coordinates

This generic construction is shared by all three forms β_A, β_B, β_C
in a finite two-sorted Folkman amalgamation diagram.  It uses the
verified finite-atom equivalences and the inverse addition laws, so
that the bilinearity hypotheses are preserved without choosing bases.

No non-unital embedding is assumed to preserve top, and a ring sort
may be the one-element zero ring.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical symmDiff

/-- Write a pairing on two native finite Boolean-ring carriers in
their canonical finite-atom powerset coordinates. -/
noncomputable def folkmanNativeTransportPairing
    {L R : Type*}
    [BooleanRing L] [Fintype L]
    [BooleanRing R] [Fintype R]
    (γ : L → R → F2) :
    Finset (PrebananaAbstractAtoms (AsBoolAlg L)) →
      Finset (PrebananaAbstractAtoms (AsBoolAlg R)) → F2 :=
  fun x y =>
    γ ((folkmanNativeRingAtomEquiv L).symm x)
      ((folkmanNativeRingAtomEquiv R).symm y)

/-- A native pairing additive on its left carrier is still additive
with symmetric difference on the left atom subsets. -/
theorem folkmanNativeTransportPairing_add_left
    {L R : Type*}
    [BooleanRing L] [Fintype L]
    [BooleanRing R] [Fintype R]
    (γ : L → R → F2)
    (hleft : ∀ x x' y, γ (x + x') y = γ x y + γ x' y)
    (s s' : Finset (PrebananaAbstractAtoms (AsBoolAlg L)))
    (t : Finset (PrebananaAbstractAtoms (AsBoolAlg R))) :
    folkmanNativeTransportPairing γ (symmDiff s s') t =
      folkmanNativeTransportPairing γ s t +
        folkmanNativeTransportPairing γ s' t := by
  unfold folkmanNativeTransportPairing
  rw [folkmanNativeRingAtomEquiv_symm_symmDiff]
  exact hleft _ _ _

/-- The analogous right-additivity transfer. -/
theorem folkmanNativeTransportPairing_add_right
    {L R : Type*}
    [BooleanRing L] [Fintype L]
    [BooleanRing R] [Fintype R]
    (γ : L → R → F2)
    (hright : ∀ x y y', γ x (y + y') = γ x y + γ x y')
    (s : Finset (PrebananaAbstractAtoms (AsBoolAlg L)))
    (t t' : Finset (PrebananaAbstractAtoms (AsBoolAlg R))) :
    folkmanNativeTransportPairing γ s (symmDiff t t') =
      folkmanNativeTransportPairing γ s t +
        folkmanNativeTransportPairing γ s t' := by
  unfold folkmanNativeTransportPairing
  rw [folkmanNativeRingAtomEquiv_symm_symmDiff]
  exact hright _ _ _

/-- Pairing transport does not alter its value on the atom codes
of actual elements of the two native ring carriers. -/
theorem folkmanNativeTransportPairing_apply_codes
    {L R : Type*}
    [BooleanRing L] [Fintype L]
    [BooleanRing R] [Fintype R]
    (γ : L → R → F2)
    (x : L) (y : R) :
    folkmanNativeTransportPairing γ
        (folkmanNativeRingAtomEquiv L x)
        (folkmanNativeRingAtomEquiv R y) = γ x y := by
  simp [folkmanNativeTransportPairing]

end SuccessorTree.NonPrecompact
