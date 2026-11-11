import BANANA.NonPrecompact.FolkmanFinitePairedBridgeSwap
import BANANA.NonPrecompact.FolkmanInitialBridgeFromAtlas
import BANANA.NonPrecompact.FolkmanGlobalProfileInvariance

/-!
# Folkman orbit classification from TWO source-side one-point extensions

The source/target-copy symmetry of a finite paired bridge means that
the one-point extension property for both copies need not be proved
separately. One source-left and one source-right extension property
imply all four requirements of the existing cofinal-chain argument.

With a countable ambient pairing and a directed finite-stage atlas,
the finite generated isomorphism determines an initial paired bridge.
The two source-side extension properties then give actual global
generated homogeneity. Genuine global automorphism-orbit equivalence
is exactly equality of the corresponding full tuple profile.

The existence of a countable Folkman limit and its two source-side
extension properties are NOT asserted or constructed here.
-/

namespace SuccessorTree.NonPrecompact

/-- An atlas, countability and two genuine one-point source extensions
are enough to extend every finite generated two-sort isomorphism to
a global pairing-preserving non-unital ring automorphism. -/
theorem folkmanGeneratedHomogeneous_of_atlas_forth
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    [Countable L] [Countable R]
    {β : L → R → F2}
    (A : FolkmanDirectedFiniteStageAtlas L R β)
    (H : FolkmanFinitePairedBridgeForthExtension L R β) :
    FolkmanGeneratedHomogeneous L R β :=
  folkmanGeneratedHomogeneous_of_atlas_onePoint
    A H.toOnePointExtension

/-- Complete finite profiles classify TRUE global automorphism
orbits on pairs of ordered left/right tuples, subject only to the
two original source-side one-point extension requirements. -/
theorem folkmanGlobalTupleRelated_iff_profile_eq_of_atlas_forth
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    [Countable L] [Countable R]
    {β : L → R → F2}
    (A : FolkmanDirectedFiniteStageAtlas L R β)
    (H : FolkmanFinitePairedBridgeForthExtension L R β)
    {nL nR : ℕ}
    (p q : (Fin nL → L) × (Fin nR → R)) :
    folkmanGlobalTupleRelated β p q ↔
      A.tupleProfile p.1 p.2 = A.tupleProfile q.1 q.2 :=
  folkmanGlobalTupleRelated_iff_profile_eq
    A (folkmanGeneratedHomogeneous_of_atlas_forth A H) p q

/-- The same reduction covers arbitrary mixed-sort tuples; their
sort labels are included in the finite complete tagged profile. -/
theorem folkmanGlobalTaggedRelated_iff_profile_eq_of_atlas_forth
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    [Countable L] [Countable R]
    {β : L → R → F2}
    (A : FolkmanDirectedFiniteStageAtlas L R β)
    (H : FolkmanFinitePairedBridgeForthExtension L R β)
    {n : ℕ}
    (p q : FolkmanTaggedStageTuple L R n) :
    folkmanGlobalTaggedRelated β p q ↔
      A.taggedProfile p = A.taggedProfile q :=
  folkmanGlobalTaggedRelated_iff_profile_eq
    A (folkmanGeneratedHomogeneous_of_atlas_forth A H) p q

/-- Finitely many actual global automorphism orbits of each
ordered pair of tuple lengths. -/
theorem folkmanGlobalTupleOrbits_finite_of_atlas_forth
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    [Countable L] [Countable R]
    {β : L → R → F2}
    (A : FolkmanDirectedFiniteStageAtlas L R β)
    (H : FolkmanFinitePairedBridgeForthExtension L R β)
    (nL nR : ℕ) :
    Finite (Quotient (folkmanGlobalTupleSetoid β nL nR)) :=
  folkmanGlobalTupleOrbits_finite_of_generatedHomogeneity
    A (folkmanGeneratedHomogeneous_of_atlas_forth A H) nL nR

/-- Finitely many genuine mixed-sort global automorphism orbits. -/
theorem folkmanGlobalTaggedOrbits_finite_of_atlas_forth
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    [Countable L] [Countable R]
    {β : L → R → F2}
    (A : FolkmanDirectedFiniteStageAtlas L R β)
    (H : FolkmanFinitePairedBridgeForthExtension L R β)
    (n : ℕ) :
    Finite (Quotient (folkmanGlobalTaggedSetoid β n)) :=
  folkmanGlobalTaggedOrbits_finite_of_generatedHomogeneity
    A (folkmanGeneratedHomogeneous_of_atlas_forth A H) n

end SuccessorTree.NonPrecompact
