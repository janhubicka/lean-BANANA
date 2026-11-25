import BANANA.NonPrecompact.FolkmanFirstOrderOrbits
import BANANA.NonPrecompact.FolkmanFirstOrderDecodingLimit
import BANANA.NonPrecompact.FolkmanFirstOrderTaggedOrbits

/-!
# Finite mixed-sort tuple orbits of the native Folkman limit
-/

namespace SuccessorTree.NonPrecompact.FolkmanDecoding

open FirstOrder CategoryTheory

/-- For each length, finitely many tuples represent all pairing-preserving
automorphism orbits in the disjoint union of the limit's native sorts. -/
theorem folkmanFirstOrderLimit_exists_finite_tagged_tuple_orbit_representatives
    (M : Bundled.{0} folkmanLanguage.Structure) [Countable M]
    (hM : Language.IsFraisseLimit folkmanFirstOrderClass M) (n : ℕ) :
    let hD : FactorsThroughPairedProducts M :=
      folkmanFirstOrderLimit_factorsThroughPairedProducts M hM
    ∃ reps : Finset (TaggedTuple M hD n),
      ∀ s : TaggedTuple M hD n, ∃ t ∈ reps, TaggedOrbit M hD s t := by
  let _ := folkmanFirstOrderLimit_tupleOrbits_finite M hM n
  exact exists_finite_tagged_tuple_orbit_representatives_of_invariant M
    (folkmanFirstOrderLimit_factorsThroughPairedProducts M hM)
    (Quotient.mk (folkmanFirstOrderTupleOrbit M n)) (fun _ _ h => Quotient.exact h)

end SuccessorTree.NonPrecompact.FolkmanDecoding
