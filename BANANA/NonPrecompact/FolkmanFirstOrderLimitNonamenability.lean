import BANANA.NonPrecompact.FolkmanIntervalStoneAction
import BANANA.NonPrecompact.FolkmanFirstOrderInterval
import BANANA.NonPrecompact.FolkmanNativePointwiseAutomorphism

/-!
# Nonamenability of the encoded Folkman–BANANA limit

The chosen nonzero left element has an interval containing a three-atom
copy. Homogeneity makes the interval's proper nonzero elements conjugate
by its point stabilizer. Its Stone action admits no invariant probability,
and amenability descends to this open subgroup.
-/

namespace SuccessorTree.NonPrecompact.FolkmanDecoding

open FirstOrder CategoryTheory BooleanBanana
open scoped FirstOrder

variable (M : Bundled.{0} folkmanLanguage.Structure) [Countable M]

/-- The actual full pointwise automorphism group of an encoded countable
Folkman Fraïssé limit is not topologically amenable. -/
theorem folkmanFirstOrderLimit_not_amenable
    (hM : Language.IsFraisseLimit folkmanFirstOrderClass M) :
    ¬ IsTopologicallyAmenable (FirstOrderAut folkmanLanguage M) := by
  let hD : FactorsThroughPairedProducts M := folkmanFirstOrderLimit_factorsThroughPairedProducts M hM
  obtain ⟨a, ha⟩ := folkmanLeftSort_exists_nonzero M hD hM
  obtain ⟨f, hf, hfa⟩ := folkmanLeftElement_exists_finiteIntervalEmbedding M hD hM a ha 3 (by decide)
  exact not_amenable_of_leftInterval M hD a ha
    (fun x y => folkmanLeftInterval_stabilizer_transitive M hD hM a x y) f hf hfa

/-- Nonamenability also holds for the native pair of automorphism sorts
with the topology of pointwise convergence on both ring carriers. -/
theorem folkmanNativeLimit_not_amenable
    (hM : Language.IsFraisseLimit folkmanFirstOrderClass M) :
    let hD : FactorsThroughPairedProducts M := folkmanFirstOrderLimit_factorsThroughPairedProducts M hM
    ¬ IsTopologicallyAmenable (folkmanPairedAutomorphisms (pairing M hD)) := by
  let hD : FactorsThroughPairedProducts M := folkmanFirstOrderLimit_factorsThroughPairedProducts M hM
  change ¬ IsTopologicallyAmenable (folkmanPairedAutomorphisms (pairing M hD))
  intro hAmen
  let p := pairing M hD
  let c := encodingEquiv M hD
  exact folkmanFirstOrderLimit_not_amenable M hM
    (amenability_of_continuousSurjectiveHom (nativePairedToEncoded p c)
      (nativePairedToEncoded_continuous p c) (nativePairedToEncoded_surjective p c) hAmen)

end SuccessorTree.NonPrecompact.FolkmanDecoding
