import BANANA.NonPrecompact.FolkmanBilinearExtension

/-!
# One certificate for the canonical Folkman bilinear extension

The existing zero-cross-block matrix construction preserves the two
pairings on their whole source coordinate spaces (not just on the common
base), and adds zero on all fresh ambient blocks.

This file collects the exact restrictions and zero-block assertions
into a single existential theorem.  The final step of transporting
these canonical coordinates back to the actual Boolean-ring atom-grid
amalgam is NOT part of this certificate.
-/

namespace SuccessorTree.NonPrecompact

/-- Compatible rectangular pairing matrices admit a common extension.
The extension restricts to all of B and C, vanishes on mixed
B-complement/C-complement blocks, and vanishes whenever an ambient
complement coordinate occurs. -/
theorem folkmanCanonicalPairingExtension_exists
    {LA RA UB VB UC VC XL XR : Type*}
    (B : Matrix (Sum LA UB) (Sum RA VB) F2)
    (C : Matrix (Sum LA UC) (Sum RA VC) F2)
    (hcommon :
      ∀ a r, B (.inl a) (.inl r) = C (.inl a) (.inl r)) :
    ∃ D : Matrix
        (Sum (Sum LA (Sum UB UC)) XL)
        (Sum (Sum RA (Sum VB VC)) XR) F2,
      D.submatrix
        (folkmanAmalgamIndexLeft :
          Sum LA UB → Sum (Sum LA (Sum UB UC)) XL)
        (folkmanAmalgamIndexLeft :
          Sum RA VB → Sum (Sum RA (Sum VB VC)) XR) = B ∧
      D.submatrix
        (folkmanAmalgamIndexRight :
          Sum LA UC → Sum (Sum LA (Sum UB UC)) XL)
        (folkmanAmalgamIndexRight :
          Sum RA VC → Sum (Sum RA (Sum VB VC)) XR) = C ∧
      (∀ u : UB, ∀ v : VC,
        D (.inl (.inr (.inl u))) (.inl (.inr (.inr v))) = 0) ∧
      (∀ u : UC, ∀ v : VB,
        D (.inl (.inr (.inr u))) (.inl (.inr (.inl v))) = 0) ∧
      (∀ x : XL, ∀ j,
        D (.inr x) j = 0) ∧
      (∀ i, ∀ y : XR,
        D i (.inr y) = 0) := by
  refine ⟨folkmanBilinearAmalgam (XL := XL) (XR := XR) B C,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact folkmanBilinearAmalgam_left B C
  · exact folkmanBilinearAmalgam_right B C hcommon
  · intro u v
    rfl
  · intro u v
    rfl
  · intro x j
    exact matrixExtendZero_extra_left (bananaBlockAmalgam B C) x j
  · intro i y
    exact matrixExtendZero_extra_right (bananaBlockAmalgam B C) i y

end SuccessorTree.NonPrecompact
