import BANANA.NonPrecompact.FolkmanFirstOrderDecoding
import BANANA.NonPrecompact.FolkmanFirstOrderClass

/-!
# Recovering native Folkman sorts from the encoded Fraïssé limit
-/

namespace SuccessorTree.NonPrecompact.FolkmanDecoding

open FirstOrder CategoryTheory

/-- Every finite tuple of the encoded Fraïssé limit admits the native
paired-product factorisation used by the decoder. -/
theorem folkmanFirstOrderLimit_factorsThroughPairedProducts
    (M : Bundled.{0} folkmanLanguage.Structure) [Countable M]
    (hM : Language.IsFraisseLimit folkmanFirstOrderClass M) :
    FactorsThroughPairedProducts M := by
  intro n xs
  obtain ⟨A, e, ys, he⟩ := folkmanFirstOrderLimit_tuple_factors M hM xs
  let P : PairedProduct := {
    Left := FolkmanNativeCodeRing A.leftCount
    Right := FolkmanNativeCodeRing A.rightCount
    leftRing := inferInstance
    rightRing := inferInstance
    data := folkmanNativeCodeRealisation A }
  exact ⟨P, e, ys, he⟩

end SuccessorTree.NonPrecompact.FolkmanDecoding
