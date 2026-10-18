import BANANA.NonPrecompact.FolkmanFiniteTwoSortRingDiagram

/-!
# A retraction-based pairing extension for Folkman--BANANA

This is the algebraic cancellation step of the explicit pivot-atom
extension construction.  On each of the two Boolean-ring sorts, the
actual atom-grid amalgam is to supply three additive retractions:
to the B-side, the C-side and the common base.

The formula below is a genuine pairing on the destination *carrier*
once those retractions are supplied.  Its restrictions to the two
source embeddings recover the entire prescribed pairings.

The retraction identities are explicit assumptions here, not hidden
claims about the atom-grid amalgam.  Their verification on actual
Boolean-ring atom subsets is a separate upcoming task.
-/

namespace SuccessorTree.NonPrecompact

/-- The common-base correction to the sum of the two pullback pairings.
In characteristic two the correction is added rather than subtracted. -/
def folkmanPairingFromRetractions
    {AL BL CL DL AR BR CR DR : Type*}
    (βA : AL → AR → F2)
    (βB : BL → BR → F2)
    (βC : CL → CR → F2)
    (ρAL : DL → AL) (ρAR : DR → AR)
    (ρBL : DL → BL) (ρBR : DR → BR)
    (ρCL : DL → CL) (ρCR : DR → CR)
    (x : DL) (y : DR) : F2 :=
  βB (ρBL x) (ρBR y) +
  βC (ρCL x) (ρCR y) +
  βA (ρAL x) (ρAR y)

/-- The B-side pairing is recovered on *every* pair of source elements
provided the pivots give source and cross-base retraction identities. -/
theorem folkmanPairingFromRetractions_left
    {AL BL CL DL AR BR CR DR : Type*}
    (βA : AL → AR → F2)
    (βB : BL → BR → F2)
    (βC : CL → CR → F2)
    (ρAL : DL → AL) (ρAR : DR → AR)
    (ρBL : DL → BL) (ρBR : DR → BR)
    (ρCL : DL → CL) (ρCR : DR → CR)
    (iBL : BL → DL) (iBR : BR → DR)
    (jCL : AL → CL) (jCR : AR → CR)
    (hBL : ∀ x, ρBL (iBL x) = x)
    (hBR : ∀ y, ρBR (iBR y) = y)
    (hCL : ∀ x, ρCL (iBL x) = jCL (ρAL (iBL x)))
    (hCR : ∀ y, ρCR (iBR y) = jCR (ρAR (iBR y)))
    (hcommon : ∀ a r, βC (jCL a) (jCR r) = βA a r)
    (x : BL) (y : BR) :
    folkmanPairingFromRetractions
      βA βB βC ρAL ρAR ρBL ρBR ρCL ρCR
      (iBL x) (iBR y) = βB x y := by
  unfold folkmanPairingFromRetractions
  rw [hBL x, hBR y, hCL x, hCR y]
  rw [hcommon (ρAL (iBL x)) (ρAR (iBR y))]
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

/-- The corresponding preservation of the complete C-side pairing. -/
theorem folkmanPairingFromRetractions_right
    {AL BL CL DL AR BR CR DR : Type*}
    (βA : AL → AR → F2)
    (βB : BL → BR → F2)
    (βC : CL → CR → F2)
    (ρAL : DL → AL) (ρAR : DR → AR)
    (ρBL : DL → BL) (ρBR : DR → BR)
    (ρCL : DL → CL) (ρCR : DR → CR)
    (iCL : CL → DL) (iCR : CR → DR)
    (jBL : AL → BL) (jBR : AR → BR)
    (hCL : ∀ x, ρCL (iCL x) = x)
    (hCR : ∀ y, ρCR (iCR y) = y)
    (hBL : ∀ x, ρBL (iCL x) = jBL (ρAL (iCL x)))
    (hBR : ∀ y, ρBR (iCR y) = jBR (ρAR (iCR y)))
    (hcommon : ∀ a r, βB (jBL a) (jBR r) = βA a r)
    (x : CL) (y : CR) :
    folkmanPairingFromRetractions
      βA βB βC ρAL ρAR ρBL ρBR ρCL ρCR
      (iCL x) (iCR y) = βC x y := by
  unfold folkmanPairingFromRetractions
  rw [hCL x, hCR y, hBL x, hBR y]
  rw [hcommon (ρAL (iCL x)) (ρAR (iCR y))]
  rw [add_left_comm, CharTwo.add_self_eq_zero, zero_add]

end SuccessorTree.NonPrecompact
