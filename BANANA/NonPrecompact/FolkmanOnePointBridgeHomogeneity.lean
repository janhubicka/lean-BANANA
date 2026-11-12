import BANANA.NonPrecompact.FolkmanFinitePairedBridgeToCofinalChain
import BANANA.NonPrecompact.FolkmanCofinalBridgeHomogeneity

/-!
# From finite one-point extensions to global Folkman homogeneity

The source-level global automorphism theorem currently requires an
exhaustive coherent finite bridge chain. The cofinal-sequence theorem
reduces this to four one-point extension properties on finite
paired bridges, provided we can start from a finite paired bridge
representing the specified isomorphism of generated structures.

This file performs that final implication. The two exact inputs
are not asserted to hold in any unconstructed countable limit.
No unit is inserted into the ambient rings or their embeddings.
-/

namespace SuccessorTree.NonPrecompact

/-- A finite paired bridge genuinely represents the prescribed
isomorphism of named ambient tuples in both original sorts. -/
structure FolkmanInitialPairedBridgeTupleWitness
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    (P : FolkmanFinitePairedBridge L R β)
    {nL nR : ℕ}
    (p q : (Fin nL → L) × (Fin nR → R)) where
  leftCoordinates : Fin nL →
    AsBoolRing (Finset (Fin P.source.atom.leftCount))
  rightCoordinates : Fin nR →
    AsBoolRing (Finset (Fin P.source.atom.rightCount))
  source_left : ∀ i, P.source.left (leftCoordinates i) = p.1 i
  target_left : ∀ i, P.targetLeft (leftCoordinates i) = q.1 i
  source_right : ∀ j, P.source.right (rightCoordinates j) = p.2 j
  target_right : ∀ j, P.targetRight (rightCoordinates j) = q.2 j

/-- Initial finite bridge availability for EVERY actual isomorphism
between the finitely generated non-unital two-sort substructures.
The finite class and intrinsic-unit interface must ultimately
supply this from the established Fraisse age. -/
def FolkmanHasInitialPairedBridges
    (L R : Type*) [NonUnitalRing L] [NonUnitalRing R]
    (β : L → R → F2) : Prop :=
  ∀ {nL nR : ℕ}
    (p q : (Fin nL → L) × (Fin nR → R)),
    FolkmanAmbientGeneratedTwoSortIso β β p.1 p.2 q.1 q.2 →
      ∃ P : FolkmanFinitePairedBridge L R β,
        Nonempty (FolkmanInitialPairedBridgeTupleWitness P p q)

/-- Countability, all four one-point finite bridge extensions and
initial bridge availability yield the previously isolated
cofinal-exhaustion property for every labelled generated isomorphism.

The construction is the monotone sequence of finite paired bridges
built by Order.sequenceOfCofinals; the initial index retains the
given tuple map while both source and target copies exhaust both
ambient sorts. -/
theorem folkmanHasCofinalBridgeExtensions_of_onePoint
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    [Countable L] [Countable R]
    {β : L → R → F2}
    (H : FolkmanFinitePairedBridgeOnePointExtension L R β)
    (hInitial : FolkmanHasInitialPairedBridges L R β) :
    FolkmanHasCofinalBridgeExtensions L R β := by
  classical
  intro nL nR p q e
  obtain ⟨initial, ⟨w⟩⟩ := hInitial p q e
  obtain ⟨chain, hzero, hmono, hSL, hTL, hSR, hTR⟩ :=
    H.exists_exhaustive_chain initial
  let C : FolkmanCofinalBridgeChain L R β :=
    folkmanCofinalBridgeChain_of_monotone
      chain hmono hSL hTL hSR hTR
  let w0 : FolkmanInitialPairedBridgeTupleWitness (chain 0) p q :=
    hzero.symm ▸ w
  refine ⟨C, ⟨{
    stage := 0
    leftCoordinates := w0.leftCoordinates
    rightCoordinates := w0.rightCoordinates
    source_left := ?_
    target_left := ?_
    source_right := ?_
    target_right := ?_
  }⟩⟩
  · intro i
    change (chain 0).source.left (w0.leftCoordinates i) = p.1 i
    exact w0.source_left i
  · intro i
    change (chain 0).targetLeft (w0.leftCoordinates i) = q.1 i
    exact w0.target_left i
  · intro j
    change (chain 0).source.right (w0.rightCoordinates j) = p.2 j
    exact w0.source_right j
  · intro j
    change (chain 0).targetRight (w0.rightCoordinates j) = q.2 j
    exact w0.target_right j

/-- All actual finite generated isomorphisms extend to global
pairing automorphisms once one-point extension and initial bridge
existence are established for the countable model. -/
theorem folkmanGeneratedHomogeneous_of_onePoint
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    [Countable L] [Countable R]
    {β : L → R → F2}
    (H : FolkmanFinitePairedBridgeOnePointExtension L R β)
    (hInitial : FolkmanHasInitialPairedBridges L R β) :
    FolkmanGeneratedHomogeneous L R β :=
  folkmanGeneratedHomogeneous_of_cofinalBridgeExtensions
    (folkmanHasCofinalBridgeExtensions_of_onePoint H hInitial)

/-- True global orbits on two-sorted tuple pairs are finite under
the two concrete one-point/initial-bridge assumptions and the
already required finite-stage atlas. -/
theorem folkmanGlobalTupleOrbits_finite_of_onePoint
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    [Countable L] [Countable R]
    {β : L → R → F2}
    (A : FolkmanDirectedFiniteStageAtlas L R β)
    (H : FolkmanFinitePairedBridgeOnePointExtension L R β)
    (hInitial : FolkmanHasInitialPairedBridges L R β)
    (nL nR : ℕ) :
    Finite (Quotient (folkmanGlobalTupleSetoid β nL nR)) :=
  folkmanGlobalTupleOrbits_finite_of_generatedHomogeneity A
    (folkmanGeneratedHomogeneous_of_onePoint H hInitial) nL nR

/-- The same assumptions imply genuine mixed-sort orbit finiteness,
not merely finiteness under an unrelated group action. -/
theorem folkmanGlobalTaggedOrbits_finite_of_onePoint
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    [Countable L] [Countable R]
    {β : L → R → F2}
    (A : FolkmanDirectedFiniteStageAtlas L R β)
    (H : FolkmanFinitePairedBridgeOnePointExtension L R β)
    (hInitial : FolkmanHasInitialPairedBridges L R β)
    (n : ℕ) :
    Finite (Quotient (folkmanGlobalTaggedSetoid β n)) :=
  folkmanGlobalTaggedOrbits_finite_of_generatedHomogeneity A
    (folkmanGeneratedHomogeneous_of_onePoint H hInitial) n

end SuccessorTree.NonPrecompact
