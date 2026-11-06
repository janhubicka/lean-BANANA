import BANANA.NonPrecompact.FolkmanNativeFiniteProfileTransport
import BANANA.NonPrecompact.FolkmanTupleProfilesPairingTransport

/-!
# Profile naturality for explicitly presented native Folkman embeddings

An embedding of finite native Boolean rings is not determined by the
existence of an unrelated atom-code embedding: the latter must induce
the given original embedding on every native ring element.

We record this exact compatibility through the left and right partial
owner maps. Together with the finite-pairing reconstruction formula,
it gives both pairing preservation on the original carriers and
invariance of the complete two-sort tuple profile.

The interface is deliberately separate from the unverified finite
index construction of draft PR #305. That construction should return
this data, not merely Nonempty of an atom-code embedding.

No countable Fraïssé limit, homogeneity, orbit-completeness or
omega-categoricity conclusion is assumed or proved here.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical BigOperators

/-- A native two-sort map together with its *specified* atom-coordinate
representation, retaining the owner fibres of each given ring map.

The atom-level embedding contains nonempty source fibres and preservation
of the full F₂ incidence matrix modulo two. The code equations are
required on every source element, not just its labelled generators. -/
structure FolkmanPresentedNativeEmbedding
    {LA RA LB RB : Type*}
    [BooleanRing LA] [BooleanRing RA]
    [BooleanRing LB] [BooleanRing RB]
    {γA : LA → RA → F2} {γB : LB → RB → F2}
    (P : FolkmanFinitePairingPresentation LA RA γA)
    (Q : FolkmanFinitePairingPresentation LB RB γB) where
  left : LA →ₙ+* LB
  right : RA →ₙ+* RB
  atomEmbedding : FolkmanAtomEmbedding P.atom Q.atom
  left_code : ∀ x : LA,
    Q.leftCode.encode (left x) =
      (P.leftCode.encode x).biUnion
        (folkmanFiber atomEmbedding.leftOwner)
  right_code : ∀ y : RA,
    Q.rightCode.encode (right y) =
      (P.rightCode.encode y).biUnion
        (folkmanFiber atomEmbedding.rightOwner)

/-- The original pairing is preserved automatically by the compatible
finite atom embedding. No extra unitality or scalar conditions occur. -/
theorem FolkmanPresentedNativeEmbedding.preserves_pairing
    {LA RA LB RB : Type*}
    [BooleanRing LA] [BooleanRing RA]
    [BooleanRing LB] [BooleanRing RB]
    {γA : LA → RA → F2} {γB : LB → RB → F2}
    {P : FolkmanFinitePairingPresentation LA RA γA}
    {Q : FolkmanFinitePairingPresentation LB RB γB}
    (E : FolkmanPresentedNativeEmbedding P Q)
    (x : LA) (y : RA) :
    γB (E.left x) (E.right y) = γA x y := by
  classical
  calc
    γB (E.left x) (E.right y) =
        ∑ i ∈ Q.leftCode.encode (E.left x),
          ∑ j ∈ Q.rightCode.encode (E.right y),
            Q.atom.edge i j :=
      Q.pairing_code _ _
    _ = ∑ i ∈
          (P.leftCode.encode x).biUnion
            (folkmanFiber E.atomEmbedding.leftOwner),
          ∑ j ∈
            (P.rightCode.encode y).biUnion
              (folkmanFiber E.atomEmbedding.rightOwner),
            Q.atom.edge i j := by
        rw [E.left_code x, E.right_code y]
    _ = ∑ a ∈ P.leftCode.encode x,
          ∑ b ∈ P.rightCode.encode y, P.atom.edge a b :=
      folkmanTupleOwnerPairing_sum E.atomEmbedding _ _
    _ = γA x y := (P.pairing_code _ _).symm

/-- Native tuple profiles are preserved by explicitly compatible
two-sort embeddings. In particular, no target atom with owner none
contributes to any nonzero generated membership signature. -/
theorem FolkmanPresentedNativeEmbedding.tupleProfile_preserved
    {LA RA LB RB : Type*}
    [BooleanRing LA] [BooleanRing RA]
    [BooleanRing LB] [BooleanRing RB]
    {γA : LA → RA → F2} {γB : LB → RB → F2}
    {P : FolkmanFinitePairingPresentation LA RA γA}
    {Q : FolkmanFinitePairingPresentation LB RB γB}
    (E : FolkmanPresentedNativeEmbedding P Q)
    {nL nR : ℕ}
    (xs : Fin nL → LA) (ys : Fin nR → RA) :
    Q.tupleProfile (fun i => E.left (xs i))
        (fun j => E.right (ys j)) =
      P.tupleProfile xs ys := by
  classical
  change folkmanAtomTupleProfile Q.atom
      (fun i => Q.leftCode.encode (E.left (xs i)))
      (fun j => Q.rightCode.encode (E.right (ys j))) =
    folkmanAtomTupleProfile P.atom
      (fun i => P.leftCode.encode (xs i))
      (fun j => P.rightCode.encode (ys j))
  have hleft :
      (fun i : Fin nL => Q.leftCode.encode (E.left (xs i))) =
        folkmanTupleOwnerImage E.atomEmbedding.leftOwner
          (fun i => P.leftCode.encode (xs i)) := by
    funext i
    change Q.leftCode.encode (E.left (xs i)) =
      (P.leftCode.encode (xs i)).biUnion
        (folkmanFiber E.atomEmbedding.leftOwner)
    exact E.left_code (xs i)
  have hright :
      (fun j : Fin nR => Q.rightCode.encode (E.right (ys j))) =
        folkmanTupleOwnerImage E.atomEmbedding.rightOwner
          (fun j => P.rightCode.encode (ys j)) := by
    funext j
    change Q.rightCode.encode (E.right (ys j)) =
      (P.rightCode.encode (ys j)).biUnion
        (folkmanFiber E.atomEmbedding.rightOwner)
    exact E.right_code (ys j)
  rw [hleft, hright]
  exact E.atomEmbedding.tupleProfile_preserved
    (fun i => P.leftCode.encode (xs i))
    (fun j => P.rightCode.encode (ys j))

end SuccessorTree.NonPrecompact
