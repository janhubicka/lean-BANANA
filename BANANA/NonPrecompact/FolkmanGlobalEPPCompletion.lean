import BANANA.NonPrecompact.FolkmanFiniteSourceHullsFromAtlas

/-!
# Final conditional Folkman orbit theorem from finite EPP

All finite algebraic reductions have been assembled:

1. A directed finite-stage atlas covers each finite original-language
   tuple and makes complete finite profiles stage independent.
2. A full finite hull containing the source copy of any finite paired
   bridge and one requested ambient element follows from the atlas.
3. An ordinary finite code embedding-extension property (EPP) extends
   the *other* copy of that bridge, hence supplies two source-side
   one-point extensions.
4. Swapping the two copies gives the two target-side extensions.
5. The existing cofinal paired-bridge construction extends actual
   isomorphisms of finitely generated non-unital two-sort structures
   to genuine pairing-preserving global automorphisms.
6. Genuine global orbits are classified exactly by complete finite
   membership-pattern/pairing-matrix profiles.

The remaining unproved global input is the actual construction of
a COUNTABLE Folkman limit having the finite-stage atlas and EPP.
No such limit is postulated as existing in this file, and no ambient
multiplicative identity has been added. Pinned local Lean
elaboration and transitive axiom audits remain outstanding.
-/

namespace SuccessorTree.NonPrecompact

/-- The directed finite-stage atlas supplies every finite source
hull, so ordinary EPP suffices for the two forth extensions and
therefore for all four back-and-forth requirements. -/
def folkmanForthExtensions_of_atlas_EPP
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    (A : FolkmanDirectedFiniteStageAtlas L R β)
    (EPP : FolkmanFiniteCodeEPP L R β) :
    FolkmanFinitePairedBridgeForthExtension L R β :=
  folkmanFinitePairedBridgeForth_of_hulls_EPP
    A.sourceHullProperty EPP

/-- Main conditional original-language homogeneity theorem:
countable non-unital Folkman structures with a directed finite
stage atlas and finite EPP extend all isomorphisms between
finitely generated substructures to global pairing automorphisms. -/
theorem folkmanGeneratedHomogeneous_of_atlas_EPP
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    [Countable L] [Countable R]
    {β : L → R → F2}
    (A : FolkmanDirectedFiniteStageAtlas L R β)
    (EPP : FolkmanFiniteCodeEPP L R β) :
    FolkmanGeneratedHomogeneous L R β :=
  folkmanGeneratedHomogeneous_of_atlas_forth A
    (folkmanForthExtensions_of_atlas_EPP A EPP)

/-- Two ordered left/right tuple pairs lie in one TRUE global
pairing-automorphism orbit iff their finite profiles agree. -/
theorem folkmanGlobalTupleRelated_iff_profile_eq_of_atlas_EPP
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    [Countable L] [Countable R]
    {β : L → R → F2}
    (A : FolkmanDirectedFiniteStageAtlas L R β)
    (EPP : FolkmanFiniteCodeEPP L R β)
    {nL nR : ℕ}
    (p q : (Fin nL → L) × (Fin nR → R)) :
    folkmanGlobalTupleRelated β p q ↔
      A.tupleProfile p.1 p.2 = A.tupleProfile q.1 q.2 :=
  folkmanGlobalTupleRelated_iff_profile_eq A
    (folkmanGeneratedHomogeneous_of_atlas_EPP A EPP) p q

/-- Exact global orbit-profile classification for mixed-sort tuples
with their original left/right sort labels. -/
theorem folkmanGlobalTaggedRelated_iff_profile_eq_of_atlas_EPP
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    [Countable L] [Countable R]
    {β : L → R → F2}
    (A : FolkmanDirectedFiniteStageAtlas L R β)
    (EPP : FolkmanFiniteCodeEPP L R β)
    {n : ℕ}
    (p q : FolkmanTaggedStageTuple L R n) :
    folkmanGlobalTaggedRelated β p q ↔
      A.taggedProfile p = A.taggedProfile q :=
  folkmanGlobalTaggedRelated_iff_profile_eq A
    (folkmanGeneratedHomogeneous_of_atlas_EPP A EPP) p q

/-- Finitely many actual global automorphism orbits on each
two-sort tuple-pair space, assuming only the directed atlas,
countability and the finite EPP of the actual ambient pairing. -/
theorem folkmanGlobalTupleOrbits_finite_of_atlas_EPP
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    [Countable L] [Countable R]
    {β : L → R → F2}
    (A : FolkmanDirectedFiniteStageAtlas L R β)
    (EPP : FolkmanFiniteCodeEPP L R β)
    (nL nR : ℕ) :
    Finite (Quotient (folkmanGlobalTupleSetoid β nL nR)) :=
  folkmanGlobalTupleOrbits_finite_of_generatedHomogeneity
    A (folkmanGeneratedHomogeneous_of_atlas_EPP A EPP) nL nR

/-- Finite genuine mixed-sort global automorphism-orbit quotients,
ready for the standard Ryll–Nardzewski deduction once the actual
countable homogeneous Folkman limit is constructed. -/
theorem folkmanGlobalTaggedOrbits_finite_of_atlas_EPP
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    [Countable L] [Countable R]
    {β : L → R → F2}
    (A : FolkmanDirectedFiniteStageAtlas L R β)
    (EPP : FolkmanFiniteCodeEPP L R β)
    (n : ℕ) :
    Finite (Quotient (folkmanGlobalTaggedSetoid β n)) :=
  folkmanGlobalTaggedOrbits_finite_of_generatedHomogeneity
    A (folkmanGeneratedHomogeneous_of_atlas_EPP A EPP) n

end SuccessorTree.NonPrecompact
