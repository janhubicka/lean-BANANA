import BANANA.NonPrecompact.FolkmanCofinalBridgeAutomorphism
import BANANA.NonPrecompact.FolkmanGlobalGeneratedHomogeneity

/-!
# The exact remaining cofinal-chain obligation for Folkman homogeneity

The preceding module constructs a genuine global pairing automorphism
from one coherent exhaustive finite bridge chain. Here we formalise
what it means for such a chain to extend a specified isomorphism of
finitely generated substructures: a single finite bridge must already
map every labelled generator to the required image.

Thus the last unproved infinite requirement is constructing a suitable
cofinal bridge chain for *each* finite generated isomorphism. If these
chains exist, generated homogeneity and finite genuine global orbits
follow from already prepared Track C results. This module does not
assert such chains exist without a hypothesis.
-/

namespace SuccessorTree.NonPrecompact

/-- The initial mapping of a labelled tuple pair is realised inside
one of the stages of the coherent exhaustive bridge chain. -/
structure FolkmanCofinalBridgeTupleWitness
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    (C : FolkmanCofinalBridgeChain L R β)
    {nL nR : ℕ}
    (p q : (Fin nL → L) × (Fin nR → R)) where
  stage : ℕ
  leftCoordinates : Fin nL →
    AsBoolRing (Finset (Fin (C.code stage).leftCount))
  rightCoordinates : Fin nR →
    AsBoolRing (Finset (Fin (C.code stage).rightCount))
  source_left : ∀ i, C.sourceLeft stage (leftCoordinates i) = p.1 i
  target_left : ∀ i, C.targetLeft stage (leftCoordinates i) = q.1 i
  source_right : ∀ j, C.sourceRight stage (rightCoordinates j) = p.2 j
  target_right : ∀ j, C.targetRight stage (rightCoordinates j) = q.2 j

/-- A coherent exhaustive finite bridge chain realising a labelled
pair of tuples provides one actual pairing-preserving global
non-unital ring automorphism sending the source tuple to its target. -/
theorem FolkmanCofinalBridgeChain.extends_tuple
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    {nL nR : ℕ}
    (C : FolkmanCofinalBridgeChain L R β)
    {p q : (Fin nL → L) × (Fin nR → R)}
    (w : FolkmanCofinalBridgeTupleWitness C p q) :
    folkmanGlobalTupleRelated β p q := by
  refine ⟨C.globalAutomorphism, ?_, ?_⟩
  · intro i
    change C.forwardLeft (p.1 i) = q.1 i
    calc
      C.forwardLeft (p.1 i) =
          C.forwardLeft (C.sourceLeft w.stage (w.leftCoordinates i)) :=
        congrArg C.forwardLeft (w.source_left i).symm
      _ = C.targetLeft w.stage (w.leftCoordinates i) :=
        C.forwardLeft_on_stage w.stage (w.leftCoordinates i)
      _ = q.1 i := w.target_left i
  · intro j
    change C.forwardRight (p.2 j) = q.2 j
    calc
      C.forwardRight (p.2 j) =
          C.forwardRight (C.sourceRight w.stage (w.rightCoordinates j)) :=
        congrArg C.forwardRight (w.source_right j).symm
      _ = C.targetRight w.stage (w.rightCoordinates j) :=
        C.forwardRight_on_stage w.stage (w.rightCoordinates j)
      _ = q.2 j := w.target_right j

/-- Precise, concrete input required from the finite extension
construction: every finite generated two-sort isomorphism extends to
an *exhaustive coherent finite bridge chain* with an initial stage
realising the labelled generators. No automorphism is assumed here. -/
def FolkmanHasCofinalBridgeExtensions
    (L R : Type*) [NonUnitalRing L] [NonUnitalRing R]
    (β : L → R → F2) : Prop :=
  ∀ {nL nR : ℕ}
    (p q : (Fin nL → L) × (Fin nR → R)),
    FolkmanAmbientGeneratedTwoSortIso β β p.1 p.2 q.1 q.2 →
      ∃ C : FolkmanCofinalBridgeChain L R β,
        Nonempty (FolkmanCofinalBridgeTupleWitness C p q)

/-- From concrete cofinal bridge extensions to the exact generated
homogeneity property needed for the Folkman oligomorphicity theorem. -/
theorem folkmanGeneratedHomogeneous_of_cofinalBridgeExtensions
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    (h : FolkmanHasCofinalBridgeExtensions L R β) :
    FolkmanGeneratedHomogeneous L R β := by
  intro nL nR p q e
  obtain ⟨C, ⟨w⟩⟩ := h p q e
  exact C.extends_tuple w

/-- The actual global orbit quotient is finite once a directed
finite-stage atlas and the concrete cofinal bridge extension
property have been constructed. -/
theorem folkmanGlobalTupleOrbits_finite_of_cofinalBridges
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    (A : FolkmanDirectedFiniteStageAtlas L R β)
    (h : FolkmanHasCofinalBridgeExtensions L R β)
    (nL nR : ℕ) :
    Finite (Quotient (folkmanGlobalTupleSetoid β nL nR)) :=
  folkmanGlobalTupleOrbits_finite_of_generatedHomogeneity A
    (folkmanGeneratedHomogeneous_of_cofinalBridgeExtensions h) nL nR

/-- The identical concrete cofinal-bridge premise suffices for
finite *mixed-sort* global automorphism orbit quotients. -/
theorem folkmanGlobalTaggedOrbits_finite_of_cofinalBridges
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    (A : FolkmanDirectedFiniteStageAtlas L R β)
    (h : FolkmanHasCofinalBridgeExtensions L R β)
    (n : ℕ) :
    Finite (Quotient (folkmanGlobalTaggedSetoid β n)) :=
  folkmanGlobalTaggedOrbits_finite_of_generatedHomogeneity A
    (folkmanGeneratedHomogeneous_of_cofinalBridgeExtensions h) n

end SuccessorTree.NonPrecompact
