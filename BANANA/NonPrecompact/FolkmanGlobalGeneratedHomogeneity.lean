import BANANA.NonPrecompact.FolkmanAmbientGeneratedTwoSortIso
import BANANA.NonPrecompact.FolkmanGlobalPairAutomorphismOrbits
import BANANA.NonPrecompact.FolkmanGlobalTaggedAutomorphismOrbits

/-!
# A single intrinsic generated-homogeneity hypothesis for Folkman orbits

Finite tuple-profile completeness is now represented by an actual
pairing- and generator-preserving isomorphism of the original ambient
generated non-unital subrings, rather than an auxiliary finite code.

The remaining infinite model-theoretic obligation is stated once:
every such finite generated-structure isomorphism extends to a global
pair of non-unital ring automorphisms preserving the entire pairing.

Under a directed finite-stage atlas and this exact extension property,
there are finitely many genuine global automorphism orbits for every
fixed pair of tuple lengths and for all mixed-sort tuples. No
homogeneous limit is constructed in this file.
-/

namespace SuccessorTree.NonPrecompact

/-- The precise intrinsic finite-generated-substructure extension
property needed for the Folkman Fraisse limit. It quantifies over
all labelled tuple pairs and all actual generated-ring isomorphisms.

It is NOT implied by local finiteness alone, and does not follow from
profile equality in a finite nonhomogeneous ambient structure. -/
def FolkmanGeneratedHomogeneous
    (L R : Type*) [NonUnitalRing L] [NonUnitalRing R]
    (β : L → R → F2) : Prop :=
  ∀ {nL nR : ℕ}
    (p q : (Fin nL → L) × (Fin nR → R)),
    FolkmanAmbientGeneratedTwoSortIso β β p.1 p.2 q.1 q.2 →
      folkmanGlobalTupleRelated β p q

/-- A directed atlas with generated homogeneity has only finitely
many *actual global pairing-automorphism* orbits on any prescribed
pair of tuple lengths, without introducing a separate arbitrary
group-action assumption. -/
theorem folkmanGlobalTupleOrbits_finite_of_generatedHomogeneity
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    (A : FolkmanDirectedFiniteStageAtlas L R β)
    (hHom : FolkmanGeneratedHomogeneous L R β)
    (nL nR : ℕ) :
    Finite (Quotient (folkmanGlobalTupleSetoid β nL nR)) := by
  apply folkmanGlobalTupleOrbits_finite_of_finiteHomogeneity
    A nL nR
  intro p q w v e
  exact hHom p q (folkmanAmbientGeneratedTwoSortIso_of_codeIso w v e)

/-- A single global automorphism carrying both masked tuple pairs
also carries the original mixed-sort tuple whenever its sort
pattern agrees. Masking never permits a left element to become
a right element. -/
theorem folkmanGlobalTaggedRelated_of_masked_tupleRelated
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2} {n : ℕ}
    (t u : FolkmanTaggedStageTuple L R n)
    (hSort : folkmanTaggedStagePattern t =
      folkmanTaggedStagePattern u)
    (hRel : folkmanGlobalTupleRelated β
      (folkmanTaggedStageLeft t, folkmanTaggedStageRight t)
      (folkmanTaggedStageLeft u, folkmanTaggedStageRight u)) :
    folkmanGlobalTaggedRelated β t u := by
  obtain ⟨E, hLeft, hRight⟩ := hRel
  refine ⟨E, ?_⟩
  intro i
  cases ht : t i with
  | inl x =>
      cases hu : u i with
      | inl y =>
          have hxy : E.left x = y := by
            simpa [folkmanTaggedStageLeft, ht, hu] using hLeft i
          simp [FolkmanGlobalPairAutomorphism.mapTagged, ht, hu, hxy]
      | inr y =>
          have hfalse : (true : Bool) = false := by
            simpa [folkmanTaggedStagePattern, ht, hu] using
              congrFun hSort i
          cases hfalse
  | inr x =>
      cases hu : u i with
      | inl y =>
          have hfalse : (false : Bool) = true := by
            simpa [folkmanTaggedStagePattern, ht, hu] using
              congrFun hSort i
          cases hfalse
      | inr y =>
          have hxy : E.right x = y := by
            simpa [folkmanTaggedStageRight, ht, hu] using hRight i
          simp [FolkmanGlobalPairAutomorphism.mapTagged, ht, hu, hxy]

/-- The same exact generated-homogeneity property suffices for all
mixed-sort global orbit quotients; no separate extension assumption
for tagged tuples is needed. -/
theorem folkmanGlobalTaggedOrbits_finite_of_generatedHomogeneity
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    (A : FolkmanDirectedFiniteStageAtlas L R β)
    (hHom : FolkmanGeneratedHomogeneous L R β)
    (n : ℕ) :
    Finite (Quotient (folkmanGlobalTaggedSetoid β n)) := by
  apply folkmanGlobalTaggedOrbits_finite_of_finiteHomogeneity
    A n
  intro t u w v hSort e
  have hRel : folkmanGlobalTupleRelated β
      (folkmanTaggedStageLeft t, folkmanTaggedStageRight t)
      (folkmanTaggedStageLeft u, folkmanTaggedStageRight u) :=
    hHom _ _ (folkmanAmbientGeneratedTwoSortIso_of_codeIso w v e)
  exact folkmanGlobalTaggedRelated_of_masked_tupleRelated
    t u hSort hRel

end SuccessorTree.NonPrecompact
