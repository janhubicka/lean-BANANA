import BANANA.NonPrecompact.FolkmanNativeProfileNaturality

/-!
# Stage-independent finite tuple profiles in non-unital Folkman unions

A countable Folkman limit is expected to be a directed union of finite
two-sorted atom presentations. Its ambient Boolean rings may have no
multiplicative unit, so only NonUnitalRing is assumed on the limit.

A stage in this file is an actual embedding of a finite atom presentation
into the ambient two-sorted non-unital structure, with injectivity and
preservation of the cross-pairing on every pair of finite stage elements.

A directed atlas covers each finite tuple by a finite stage and gives a
joint refinement for any two stages covering that same tuple. The
existing embedding-invariance theorem for full Folkman tuple profiles
then proves independence of every choice of stage and atom labels.

This file does NOT construct the Fraisse limit, prove that an actual
Folkman limit admits such an atlas, or supply global automorphisms.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical BigOperators

/-- A faithful finite atom stage inside a possibly non-unital infinite
Folkman structure. The ring homomorphisms preserve zero, addition and
multiplication, but are not assumed to preserve ambient units. -/
structure FolkmanFiniteAtomStage
    (L R : Type*) [NonUnitalRing L] [NonUnitalRing R]
    (β : L → R → F2) where
  atom : FolkmanAtomStructure
  left : AsBoolRing (Finset (Fin atom.leftCount)) →ₙ+* L
  right : AsBoolRing (Finset (Fin atom.rightCount)) →ₙ+* R
  left_injective : Function.Injective left
  right_injective : Function.Injective right
  preserves_pairing :
    ∀ (s : Finset (Fin atom.leftCount))
      (t : Finset (Fin atom.rightCount)),
      β (left (toBoolRing s)) (right (toBoolRing t)) =
        ∑ a ∈ s, ∑ b ∈ t, atom.edge a b

/-- A finite stage-refinement map: the underlying original structure
is unchanged after passing from source to target. The equations
retain the exact embedding into the ambient rings, not just an
abstract isomorphism class of the two finite stages. -/
structure FolkmanFiniteAtomStageMap
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    (A B : FolkmanFiniteAtomStage L R β) where
  atom : FolkmanAtomEmbedding A.atom B.atom
  left_commutes : ∀ s : Finset (Fin A.atom.leftCount),
    B.left (toBoolRing (s.biUnion (folkmanFiber atom.leftOwner))) =
      A.left (toBoolRing s)
  right_commutes : ∀ t : Finset (Fin A.atom.rightCount),
    B.right (toBoolRing (t.biUnion (folkmanFiber atom.rightOwner))) =
      A.right (toBoolRing t)

/-- A pair of finite stage-refinements to one common finite stage. -/
structure FolkmanCommonFiniteStage
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    (A B : FolkmanFiniteAtomStage L R β) where
  target : FolkmanFiniteAtomStage L R β
  first : FolkmanFiniteAtomStageMap A target
  second : FolkmanFiniteAtomStageMap B target

/-- A finite stage presentation of one labelled tuple pair in the
ambient non-unital two-sorted structure. -/
structure FolkmanFiniteTupleStageWitness
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    {nL nR : ℕ}
    (xs : Fin nL → L) (ys : Fin nR → R) where
  stage : FolkmanFiniteAtomStage L R β
  leftTuple : Fin nL → Finset (Fin stage.atom.leftCount)
  rightTuple : Fin nR → Finset (Fin stage.atom.rightCount)
  left_spec : ∀ i, stage.left (toBoolRing (leftTuple i)) = xs i
  right_spec : ∀ j, stage.right (toBoolRing (rightTuple j)) = ys j

/-- The full finite two-sort profile calculated at one chosen stage. -/
noncomputable def FolkmanFiniteTupleStageWitness.profile
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    {nL nR : ℕ}
    {xs : Fin nL → L} {ys : Fin nR → R}
    (w : FolkmanFiniteTupleStageWitness xs ys) :
    FolkmanAtomTupleProfile nL nR :=
  folkmanAtomTupleProfile w.stage.atom w.leftTuple w.rightTuple

/-- A common refinement inside the same ambient non-unital structure
gives equal complete finite profiles of the same labelled tuple pair.

Both sorts may have no generated nonzero atoms. The proof uses
injectivity of the common-stage maps to compare the actual tuple
coordinates inside that stage, then the earlier full two-sort
profile-invariance theorem. -/
theorem folkmanFiniteTupleProfile_eq_of_commonStage
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    {nL nR : ℕ}
    {xs : Fin nL → L} {ys : Fin nR → R}
    (w v : FolkmanFiniteTupleStageWitness xs ys)
    (C : FolkmanCommonFiniteStage w.stage v.stage) :
    w.profile = v.profile := by
  classical
  have hleft :
      folkmanTupleOwnerImage C.first.atom.leftOwner w.leftTuple =
        folkmanTupleOwnerImage C.second.atom.leftOwner v.leftTuple := by
    funext i
    change
      (w.leftTuple i).biUnion (folkmanFiber C.first.atom.leftOwner) =
      (v.leftTuple i).biUnion (folkmanFiber C.second.atom.leftOwner)
    apply toBoolRing.injective
    apply C.target.left_injective
    calc
      C.target.left (toBoolRing
          ((w.leftTuple i).biUnion
            (folkmanFiber C.first.atom.leftOwner))) =
        w.stage.left (toBoolRing (w.leftTuple i)) :=
          C.first.left_commutes (w.leftTuple i)
      _ = xs i := w.left_spec i
      _ = v.stage.left (toBoolRing (v.leftTuple i)) :=
        (v.left_spec i).symm
      _ = C.target.left (toBoolRing
          ((v.leftTuple i).biUnion
            (folkmanFiber C.second.atom.leftOwner))) :=
          (C.second.left_commutes (v.leftTuple i)).symm
  have hright :
      folkmanTupleOwnerImage C.first.atom.rightOwner w.rightTuple =
        folkmanTupleOwnerImage C.second.atom.rightOwner v.rightTuple := by
    funext j
    change
      (w.rightTuple j).biUnion (folkmanFiber C.first.atom.rightOwner) =
      (v.rightTuple j).biUnion (folkmanFiber C.second.atom.rightOwner)
    apply toBoolRing.injective
    apply C.target.right_injective
    calc
      C.target.right (toBoolRing
          ((w.rightTuple j).biUnion
            (folkmanFiber C.first.atom.rightOwner))) =
        w.stage.right (toBoolRing (w.rightTuple j)) :=
          C.first.right_commutes (w.rightTuple j)
      _ = ys j := w.right_spec j
      _ = v.stage.right (toBoolRing (v.rightTuple j)) :=
        (v.right_spec j).symm
      _ = C.target.right (toBoolRing
          ((v.rightTuple j).biUnion
            (folkmanFiber C.second.atom.rightOwner))) :=
          (C.second.right_commutes (v.rightTuple j)).symm
  change folkmanAtomTupleProfile w.stage.atom w.leftTuple w.rightTuple =
    folkmanAtomTupleProfile v.stage.atom v.leftTuple v.rightTuple
  calc
    folkmanAtomTupleProfile w.stage.atom w.leftTuple w.rightTuple =
        folkmanAtomTupleProfile C.target.atom
          (folkmanTupleOwnerImage C.first.atom.leftOwner w.leftTuple)
          (folkmanTupleOwnerImage C.first.atom.rightOwner w.rightTuple) :=
      (C.first.atom.tupleProfile_preserved w.leftTuple w.rightTuple).symm
    _ = folkmanAtomTupleProfile C.target.atom
          (folkmanTupleOwnerImage C.second.atom.leftOwner v.leftTuple)
          (folkmanTupleOwnerImage C.second.atom.rightOwner v.rightTuple) := by
        rw [hleft, hright]
    _ = folkmanAtomTupleProfile v.stage.atom v.leftTuple v.rightTuple :=
      C.second.atom.tupleProfile_preserved v.leftTuple v.rightTuple

/-- Exact finite-stage hypotheses needed for a well-defined tuple
profile on a directed union: every labelled finite tuple is covered,
and any two of its finite presentations have a common refinement.

This is an *interface*, not a constructed Folkman Fraisse limit. -/
structure FolkmanDirectedFiniteStageAtlas
    (L R : Type*) [NonUnitalRing L] [NonUnitalRing R]
    (β : L → R → F2) where
  covers : ∀ (nL nR : ℕ)
      (xs : Fin nL → L) (ys : Fin nR → R),
    Nonempty (FolkmanFiniteTupleStageWitness (β := β) xs ys)
  common : ∀ {nL nR : ℕ}
      {xs : Fin nL → L} {ys : Fin nR → R}
      (w v : FolkmanFiniteTupleStageWitness (β := β) xs ys),
    Nonempty (FolkmanCommonFiniteStage w.stage v.stage)

/-- Choose any finite stage containing the tuple and compute the
complete profile in that finite atom presentation. -/
noncomputable def FolkmanDirectedFiniteStageAtlas.tupleProfile
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    (A : FolkmanDirectedFiniteStageAtlas L R β)
    {nL nR : ℕ}
    (xs : Fin nL → L) (ys : Fin nR → R) :
    FolkmanAtomTupleProfile nL nR :=
  (Classical.choice (A.covers nL nR xs ys)).profile

/-- The chosen profile agrees with the result in *every* finite stage
presentation of the same tuple, not just the one chosen by Classical.choice. -/
theorem FolkmanDirectedFiniteStageAtlas.tupleProfile_eq_witness
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    (A : FolkmanDirectedFiniteStageAtlas L R β)
    {nL nR : ℕ}
    (xs : Fin nL → L) (ys : Fin nR → R)
    (w : FolkmanFiniteTupleStageWitness (β := β) xs ys) :
    A.tupleProfile xs ys = w.profile := by
  classical
  let chosen : FolkmanFiniteTupleStageWitness (β := β) xs ys :=
    Classical.choice (A.covers nL nR xs ys)
  change chosen.profile = w.profile
  exact folkmanFiniteTupleProfile_eq_of_commonStage chosen w
    (Classical.choice (A.common chosen w))

/-- The codomain of this stage-independent invariant is finite for
every fixed choice of two tuple lengths. No ultrahomogeneity is claimed. -/
theorem FolkmanDirectedFiniteStageAtlas.tupleProfile_type_finite
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    (A : FolkmanDirectedFiniteStageAtlas L R β)
    (nL nR : ℕ) :
    Finite (FolkmanAtomTupleProfile nL nR) :=
  folkmanAtomTupleProfileType_finite nL nR

end SuccessorTree.NonPrecompact
