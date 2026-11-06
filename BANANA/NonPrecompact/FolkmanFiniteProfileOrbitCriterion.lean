import BANANA.NonPrecompact.FolkmanNativeFiniteProfileTransport
import BANANA.NonPrecompact.PrebananaFiniteOrbitCriterion

/-!
# Conditional Folkman tuple-orbit finiteness from finite profiles

The finite tuple-profile type was established in the Folkman finite
atom modules. The generic finite-invariant quotient argument was
already proved for pre-BANANA. We reuse that theorem unchanged.

No global countable Folkman limit or extension property is assumed:
the precise profile-to-global-orbit implication is an explicit
hypothesis and remains a separate Track B obligation.
-/

namespace SuccessorTree.NonPrecompact

/-- An arbitrary orbit or equivalence quotient is finite whenever
the complete Folkman two-sort profile separates its classes. -/
theorem folkmanFiniteProfile_quotient_finite
    {X : Type*} [s : Setoid X] (nL nR : ℕ)
    (profile : X → FolkmanAtomTupleProfile nL nR)
    (hcomplete : ∀ x y : X,
      profile x = profile y → x ≈ y) :
    Finite (Quotient s) := by
  letI : Finite (FolkmanAtomTupleProfile nL nR) :=
    folkmanAtomTupleProfileType_finite nL nR
  exact finiteQuotient_of_completeFiniteInvariant profile hcomplete

/-- In particular the global automorphism-orbit quotient is finite
provided *one* complete profile is constant enough to force actual
global automorphism conjugacy. This assertion does not construct
or assert the existence of such a group action for Folkman. -/
theorem folkmanFiniteProfile_orbits_finite
    {G X : Type*} [Group G] [MulAction G X]
    (nL nR : ℕ)
    (profile : X → FolkmanAtomTupleProfile nL nR)
    (hcomplete : ∀ x y : X,
      profile x = profile y → x ∈ MulAction.orbit G y) :
    Finite (MulAction.orbitRel.Quotient G X) := by
  letI : Setoid X := MulAction.orbitRel G X
  exact folkmanFiniteProfile_quotient_finite nL nR profile hcomplete

/-- The codomain for a *mixed-sort* tuple also includes its sort
pattern. This remains finite for each fixed tuple length. -/
abbrev FolkmanTaggedFiniteProfile (n : ℕ) :=
  (Fin n → Bool) × FolkmanAtomTupleProfile n n

theorem folkmanTaggedFiniteProfile_finite (n : ℕ) :
    Finite (FolkmanTaggedFiniteProfile n) := by
  letI : Finite (FolkmanAtomTupleProfile n n) :=
    folkmanAtomTupleProfileType_finite n n
  infer_instance

/-- A conditional global-orbit finiteness statement for arbitrary
mixed-sort tuples, retaining their pattern of left/right labels. -/
theorem folkmanTaggedFiniteProfile_orbits_finite
    {G X : Type*} [Group G] [MulAction G X]
    (n : ℕ)
    (profile : X → FolkmanTaggedFiniteProfile n)
    (hcomplete : ∀ x y : X,
      profile x = profile y → x ∈ MulAction.orbit G y) :
    Finite (MulAction.orbitRel.Quotient G X) := by
  letI : Finite (FolkmanTaggedFiniteProfile n) :=
    folkmanTaggedFiniteProfile_finite n
  letI : Setoid X := MulAction.orbitRel G X
  exact finiteQuotient_of_completeFiniteInvariant profile hcomplete

end SuccessorTree.NonPrecompact
