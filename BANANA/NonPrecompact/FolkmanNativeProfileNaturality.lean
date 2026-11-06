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

/-- An Option-valued owner with a nonempty fibre over every source
atom induces an injective inverse-image map on finite atom subsets.
This lemma also covers an empty source atom set. -/
theorem folkmanOwnerBiUnion_injective
    {q n : ℕ}
    (owner : Fin n → Option (Fin q))
    (hsurj : ∀ a : Fin q, (folkmanFiber owner a).Nonempty) :
    Function.Injective
      (fun s : Finset (Fin q) => s.biUnion (folkmanFiber owner)) := by
  classical
  intro s t h
  apply Finset.ext
  intro a
  obtain ⟨b, hb⟩ := hsurj a
  have hown : owner b = some a := (Finset.mem_filter.mp hb).2
  have hmem (u : Finset (Fin q)) :
      b ∈ u.biUnion (folkmanFiber owner) ↔ a ∈ u := by
    constructor
    · intro hu
      obtain ⟨a', ha', hb'⟩ := Finset.mem_biUnion.mp hu
      have hown' : owner b = some a' := (Finset.mem_filter.mp hb').2
      have heq : a' = a := Option.some.inj (hown'.symm.trans hown)
      exact heq ▸ ha'
    · intro ha
      exact Finset.mem_biUnion.mpr ⟨a, ha, hb⟩
  have heq :
      b ∈ s.biUnion (folkmanFiber owner) ↔
        b ∈ t.biUnion (folkmanFiber owner) := by rw [h]
  exact (hmem s).symm.trans (heq.trans (hmem t))

/-- The left original-ring map in a presented embedding is genuinely
injective; this follows from nonempty atom-owner fibres and the
faithfulness of the finite presentation, rather than being assumed. -/
theorem FolkmanPresentedNativeEmbedding.left_injective
    {LA RA LB RB : Type*}
    [BooleanRing LA] [BooleanRing RA]
    [BooleanRing LB] [BooleanRing RB]
    {γA : LA → RA → F2} {γB : LB → RB → F2}
    {P : FolkmanFinitePairingPresentation LA RA γA}
    {Q : FolkmanFinitePairingPresentation LB RB γB}
    (E : FolkmanPresentedNativeEmbedding P Q) :
    Function.Injective E.left := by
  intro x y hxy
  apply P.leftCode.encode.injective
  apply folkmanOwnerBiUnion_injective
    E.atomEmbedding.leftOwner E.atomEmbedding.left_fibre_nonempty
  calc
    (P.leftCode.encode x).biUnion
        (folkmanFiber E.atomEmbedding.leftOwner) =
      Q.leftCode.encode (E.left x) := (E.left_code x).symm
    _ = Q.leftCode.encode (E.left y) :=
      congrArg Q.leftCode.encode hxy
    _ = (P.leftCode.encode y).biUnion
        (folkmanFiber E.atomEmbedding.leftOwner) := E.left_code y

/-- Right-sort injectivity follows by the same finite-owner argument. -/
theorem FolkmanPresentedNativeEmbedding.right_injective
    {LA RA LB RB : Type*}
    [BooleanRing LA] [BooleanRing RA]
    [BooleanRing LB] [BooleanRing RB]
    {γA : LA → RA → F2} {γB : LB → RB → F2}
    {P : FolkmanFinitePairingPresentation LA RA γA}
    {Q : FolkmanFinitePairingPresentation LB RB γB}
    (E : FolkmanPresentedNativeEmbedding P Q) :
    Function.Injective E.right := by
  intro x y hxy
  apply P.rightCode.encode.injective
  apply folkmanOwnerBiUnion_injective
    E.atomEmbedding.rightOwner E.atomEmbedding.right_fibre_nonempty
  calc
    (P.rightCode.encode x).biUnion
        (folkmanFiber E.atomEmbedding.rightOwner) =
      Q.rightCode.encode (E.right x) := (E.right_code x).symm
    _ = Q.rightCode.encode (E.right y) :=
      congrArg Q.rightCode.encode hxy
    _ = (P.rightCode.encode y).biUnion
        (folkmanFiber E.atomEmbedding.rightOwner) := E.right_code y

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


/-- The finite tuple profile is independent of a finite stage whenever
two presentations of the same labelled tuple embed compatibly into
one common finite extension.

This is the exact finite-stage independence needed for an eventual
directed construction of the countable Folkman limit. It does not
construct that limit or assert that arbitrary finite stages have
already been amalgamated. -/
theorem folkmanTupleProfile_eq_of_commonPresentedExtension
    {LA RA LB RB LC RC : Type*}
    [BooleanRing LA] [BooleanRing RA]
    [BooleanRing LB] [BooleanRing RB]
    [BooleanRing LC] [BooleanRing RC]
    {γA : LA → RA → F2}
    {γB : LB → RB → F2}
    {γC : LC → RC → F2}
    {P : FolkmanFinitePairingPresentation LA RA γA}
    {Q : FolkmanFinitePairingPresentation LB RB γB}
    {C : FolkmanFinitePairingPresentation LC RC γC}
    (E : FolkmanPresentedNativeEmbedding P C)
    (F : FolkmanPresentedNativeEmbedding Q C)
    {nL nR : ℕ}
    (xsA : Fin nL → LA) (ysA : Fin nR → RA)
    (xsB : Fin nL → LB) (ysB : Fin nR → RB)
    (hleft : ∀ i, E.left (xsA i) = F.left (xsB i))
    (hright : ∀ j, E.right (ysA j) = F.right (ysB j)) :
    P.tupleProfile xsA ysA = Q.tupleProfile xsB ysB := by
  have hxs :
      (fun i : Fin nL => E.left (xsA i)) =
        (fun i => F.left (xsB i)) := by
    funext i
    exact hleft i
  have hys :
      (fun j : Fin nR => E.right (ysA j)) =
        (fun j => F.right (ysB j)) := by
    funext j
    exact hright j
  calc
    P.tupleProfile xsA ysA =
        C.tupleProfile (fun i => E.left (xsA i))
          (fun j => E.right (ysA j)) :=
      (E.tupleProfile_preserved xsA ysA).symm
    _ = C.tupleProfile (fun i => F.left (xsB i))
          (fun j => F.right (ysB j)) := by
        rw [hxs, hys]
    _ = Q.tupleProfile xsB ysB :=
      F.tupleProfile_preserved xsB ysB


/-- Profile transport through two successive *specified* native
embeddings. No composition theorem for partial atom-owner maps is
needed: stage independence follows by applying the existing exact
naturality theorem twice, with no additional assumptions.

In a directed finite-stage construction this permits refinement
through an intermediate stage, including the zero ring on either
sort. -/
theorem folkmanTupleProfile_preserved_twoStep
    {LA RA LB RB LC RC : Type*}
    [BooleanRing LA] [BooleanRing RA]
    [BooleanRing LB] [BooleanRing RB]
    [BooleanRing LC] [BooleanRing RC]
    {γA : LA → RA → F2}
    {γB : LB → RB → F2}
    {γC : LC → RC → F2}
    {P : FolkmanFinitePairingPresentation LA RA γA}
    {Q : FolkmanFinitePairingPresentation LB RB γB}
    {C : FolkmanFinitePairingPresentation LC RC γC}
    (E : FolkmanPresentedNativeEmbedding P Q)
    (F : FolkmanPresentedNativeEmbedding Q C)
    {nL nR : ℕ}
    (xs : Fin nL → LA) (ys : Fin nR → RA) :
    C.tupleProfile (fun i => F.left (E.left (xs i)))
        (fun j => F.right (E.right (ys j))) =
      P.tupleProfile xs ys := by
  calc
    C.tupleProfile (fun i => F.left (E.left (xs i)))
        (fun j => F.right (E.right (ys j))) =
      Q.tupleProfile (fun i => E.left (xs i))
        (fun j => E.right (ys j)) :=
      F.tupleProfile_preserved
        (fun i => E.left (xs i)) (fun j => E.right (ys j))
    _ = P.tupleProfile xs ys :=
      E.tupleProfile_preserved xs ys


end SuccessorTree.NonPrecompact
