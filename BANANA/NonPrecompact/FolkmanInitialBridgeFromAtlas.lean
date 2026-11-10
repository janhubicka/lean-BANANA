import BANANA.NonPrecompact.FolkmanNativeInitialPairedBridge
import BANANA.NonPrecompact.FolkmanOnePointBridgeHomogeneity
import BANANA.NonPrecompact.FolkmanAmbientGeneratedNativePairing

/-!
# Initial Folkman paired bridges from actual finite generated isomorphisms

The previous one-point back-and-forth construction assumed that
every isomorphism of two finitely generated two-sort substructures
is represented by an initial finite paired bridge.

This file supplies that initial bridge using:
* finite-stage coverage in the original ambient non-unital rings;
* the intrinsic Boolean-ring structures of generated subrings;
* Track B's native finite-object atom-code isomorphism;
* the specified generator- and pairing-preserving isomorphism
  of the two actual ambient generated substructures.

Both finite copies are images of the SAME source generated rings.
They need not extend to isomorphisms of arbitrary larger finite
ambient stages; this is why the intrinsic generated ring is used.
No global ambient unit or automorphism is assumed.

These proofs remain source-only until pinned Lean elaboration and
transitive axiom inspection.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical

/-- A directed finite-stage atlas already supplies the initial
paired bridge for every isomorphism of the actual finitely generated
Folkman substructures. The ONLY remaining countable homogeneity
input is the paired-bridge one-point extension property. -/
theorem folkmanHasInitialPairedBridges_of_atlas
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    (A : FolkmanDirectedFiniteStageAtlas L R β) :
    FolkmanHasInitialPairedBridges L R β := by
  classical
  intro nL nR p q e
  let w : FolkmanFiniteTupleStageWitness (β := β) p.1 p.2 :=
    Classical.choice (A.covers nL nR p.1 p.2)
  let SL : NonUnitalSubring L :=
    NonUnitalSubring.closure (Set.range p.1)
  let SR : NonUnitalSubring R :=
    NonUnitalSubring.closure (Set.range p.2)
  let TL : NonUnitalSubring L :=
    NonUnitalSubring.closure (Set.range q.1)
  let TR : NonUnitalSubring R :=
    NonUnitalSubring.closure (Set.range q.2)
  letI : BooleanRing SL := w.left_generatedBooleanRing
  letI : BooleanRing SR := w.right_generatedBooleanRing
  letI : Finite SL := w.left_generated_finite
  letI : Finite SR := w.right_generated_finite
  letI : Fintype SL := Fintype.ofFinite SL
  letI : Fintype SR := Fintype.ofFinite SR
  let P : FolkmanNativeFinitePairing SL SR :=
    w.generatedNativePairing A
  let I : FolkmanNativeFinitePairingIso P
      (folkmanNativeCodeRealisation (folkmanNativeFinCode P.pairing)) :=
    folkmanNativeFiniteCodeIso P
  let fL : SL →ₙ+* L := NonUnitalSubringClass.subtype SL
  let fR : SR →ₙ+* R := NonUnitalSubringClass.subtype SR
  let gL : SL →ₙ+* L :=
    (NonUnitalSubringClass.subtype TL).comp
      (e.left : SL →ₙ+* TL)
  let gR : SR →ₙ+* R :=
    (NonUnitalSubringClass.subtype TR).comp
      (e.right : SR →ₙ+* TR)
  have hfL : Function.Injective fL := Subtype.val_injective
  have hfR : Function.Injective fR := Subtype.val_injective
  have hgL : Function.Injective gL := by
    intro x y hxy
    apply e.left.injective
    exact Subtype.val_injective hxy
  have hgR : Function.Injective gR := by
    intro x y hxy
    apply e.right.injective
    exact Subtype.val_injective hxy
  have hF : ∀ x y, β (fL x) (fR y) = P.pairing x y := by
    intro x y
    rfl
  have hG : ∀ x y, β (gL x) (gR y) = P.pairing x y := by
    intro x y
    exact e.preserves_pairing x y
  let B : FolkmanFinitePairedBridge L R β :=
    folkmanFinitePairedBridge_of_nativeIso
      β P I fL fR gL gR hfL hfR hgL hgR hF hG
  refine ⟨B, ⟨{
    leftCoordinates :=
      fun i => I.left (folkmanAmbientGeneratedTupleCoordinate p.1 i)
    rightCoordinates :=
      fun j => I.right (folkmanAmbientGeneratedTupleCoordinate p.2 j)
    source_left := ?_
    target_left := ?_
    source_right := ?_
    target_right := ?_
  }⟩⟩
  · intro i
    change fL (I.left.symm
      (I.left (folkmanAmbientGeneratedTupleCoordinate p.1 i))) = p.1 i
    rw [I.left.symm_apply_apply]
    rfl
  · intro i
    change gL (I.left.symm
      (I.left (folkmanAmbientGeneratedTupleCoordinate p.1 i))) = q.1 i
    rw [I.left.symm_apply_apply]
    have h := e.left_generators i
    exact congrArg Subtype.val h
  · intro j
    change fR (I.right.symm
      (I.right (folkmanAmbientGeneratedTupleCoordinate p.2 j))) = p.2 j
    rw [I.right.symm_apply_apply]
    rfl
  · intro j
    change gR (I.right.symm
      (I.right (folkmanAmbientGeneratedTupleCoordinate p.2 j))) = q.2 j
    rw [I.right.symm_apply_apply]
    have h := e.right_generators j
    exact congrArg Subtype.val h

/-- The four one-point paired-bridge extensions are sufficient for
actual generated homogeneity of a countable non-unital Folkman
pairing equipped with a directed finite-stage atlas.

The former extra hypothesis of initial bridges is now discharged
by the finite native coding and actual generated isomorphism.
The existence of the countable limit and its one-point extension
property still must be established separately. -/
theorem folkmanGeneratedHomogeneous_of_atlas_onePoint
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    [Countable L] [Countable R]
    {β : L → R → F2}
    (A : FolkmanDirectedFiniteStageAtlas L R β)
    (H : FolkmanFinitePairedBridgeOnePointExtension L R β) :
    FolkmanGeneratedHomogeneous L R β :=
  folkmanGeneratedHomogeneous_of_onePoint H
    (folkmanHasInitialPairedBridges_of_atlas A)

/-- Finite genuine global orbit quotients, now with NO separately
postulated initial-bridge premise. -/
theorem folkmanGlobalTupleOrbits_finite_of_atlas_onePoint
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    [Countable L] [Countable R]
    {β : L → R → F2}
    (A : FolkmanDirectedFiniteStageAtlas L R β)
    (H : FolkmanFinitePairedBridgeOnePointExtension L R β)
    (nL nR : ℕ) :
    Finite (Quotient (folkmanGlobalTupleSetoid β nL nR)) :=
  folkmanGlobalTupleOrbits_finite_of_generatedHomogeneity A
    (folkmanGeneratedHomogeneous_of_atlas_onePoint A H) nL nR

/-- The same precise remaining extension premise gives
oligomorphicity for genuinely mixed-sort global automorphism
orbits. -/
theorem folkmanGlobalTaggedOrbits_finite_of_atlas_onePoint
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    [Countable L] [Countable R]
    {β : L → R → F2}
    (A : FolkmanDirectedFiniteStageAtlas L R β)
    (H : FolkmanFinitePairedBridgeOnePointExtension L R β)
    (n : ℕ) :
    Finite (Quotient (folkmanGlobalTaggedSetoid β n)) :=
  folkmanGlobalTaggedOrbits_finite_of_generatedHomogeneity A
    (folkmanGeneratedHomogeneous_of_atlas_onePoint A H) n

end SuccessorTree.NonPrecompact
