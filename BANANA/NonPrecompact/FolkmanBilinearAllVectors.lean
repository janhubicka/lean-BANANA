import BANANA.NonPrecompact.BananaStrongBlockAmalgam
import BANANA.NonPrecompact.FolkmanBilinearExtension

/-!
# Bilinear evaluation under the Folkman zero-block extension

The manuscript needs preservation of the pairing of *all elements*,
not just the basis-entry equalities of the matrix.  Extend the
canonical block matrix to the extra ambient coordinates by zero and
show that evaluation on the embedded source vectors agrees with both
original bilinear pairings.

This still uses split linear coordinates; identifying them with the
actual non-unital Boolean-ring atom-grid embeddings is separate.
-/

namespace SuccessorTree.NonPrecompact

/-- Adding zero coordinates to a finite matrix does not change
the pairing of zero-extended vectors. -/
theorem indexedBananaPairing_matrixExtendZero
    {I J XL XR : Type*}
    [Fintype I] [Fintype J] [Fintype XL] [Fintype XR]
    (M : Matrix I J F2)
    (x : I → F2) (y : J → F2) :
    indexedBananaPairing (matrixExtendZero (XL := XL) (XR := XR) M)
      (sumCommonLinear (X := XL) x)
      (sumCommonLinear (X := XR) y) =
    indexedBananaPairing M x y := by
  classical
  simp [indexedBananaPairing, Fintype.sum_sum_type,
    sumCommonLinear, matrixExtendZero]

/-- The complete B-side pairing is preserved in the ambient Folkman
matrix, for arbitrary source vectors and arbitrary extra coordinates. -/
theorem indexedBananaPairing_folkman_left
    {LA RA UB VB UC VC XL XR : Type*}
    [Fintype LA] [Fintype RA]
    [Fintype UB] [Fintype VB] [Fintype UC] [Fintype VC]
    [Fintype XL] [Fintype XR]
    (B : Matrix (Sum LA UB) (Sum RA VB) F2)
    (C : Matrix (Sum LA UC) (Sum RA VC) F2)
    (x : Sum LA UB → F2) (y : Sum RA VB → F2) :
    indexedBananaPairing
      (folkmanBilinearAmalgam (XL := XL) (XR := XR) B C)
      (folkmanAmalgamLinearLeft (Y := UC) (Z := XL) x)
      (folkmanAmalgamLinearLeft (Y := VC) (Z := XR) y) =
      indexedBananaPairing B x y := by
  change indexedBananaPairing
    (matrixExtendZero (XL := XL) (XR := XR) (bananaBlockAmalgam B C))
    (sumCommonLinear (X := XL) (sumAmalgamLinearLeft x))
    (sumCommonLinear (X := XR) (sumAmalgamLinearLeft y)) =
      indexedBananaPairing B x y
  rw [indexedBananaPairing_matrixExtendZero]
  exact indexedBananaPairing_amalgam_left B C x y

/-- The complete C-side pairing is preserved when the old pairings
agree on the common base block. -/
theorem indexedBananaPairing_folkman_right
    {LA RA UB VB UC VC XL XR : Type*}
    [Fintype LA] [Fintype RA]
    [Fintype UB] [Fintype VB] [Fintype UC] [Fintype VC]
    [Fintype XL] [Fintype XR]
    (B : Matrix (Sum LA UB) (Sum RA VB) F2)
    (C : Matrix (Sum LA UC) (Sum RA VC) F2)
    (hcommon : ∀ a r,
      B (.inl a) (.inl r) = C (.inl a) (.inl r))
    (x : Sum LA UC → F2) (y : Sum RA VC → F2) :
    indexedBananaPairing
      (folkmanBilinearAmalgam (XL := XL) (XR := XR) B C)
      (folkmanAmalgamLinearRight (X := UB) (Z := XL) x)
      (folkmanAmalgamLinearRight (X := VB) (Z := XR) y) =
      indexedBananaPairing C x y := by
  change indexedBananaPairing
    (matrixExtendZero (XL := XL) (XR := XR) (bananaBlockAmalgam B C))
    (sumCommonLinear (X := XL) (sumAmalgamLinearRight x))
    (sumCommonLinear (X := XR) (sumAmalgamLinearRight y)) =
      indexedBananaPairing C x y
  rw [indexedBananaPairing_matrixExtendZero]
  exact indexedBananaPairing_amalgam_right B C hcommon x y

end SuccessorTree.NonPrecompact
