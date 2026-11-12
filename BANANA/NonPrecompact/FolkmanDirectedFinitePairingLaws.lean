import BANANA.NonPrecompact.FolkmanDirectedFiniteStageAtlas
import BANANA.NonPrecompact.FolkmanNativeFiniteCodeRealisation

/-!
# Biadditivity of the original pairing in a directed Folkman stage atlas

The atlas interface previously required exact pairing reconstruction
on each finite atom stage, but did not explicitly expose the resulting
additivity of the ORIGINAL ambient pairing. This module derives it
from finite stage coverage, not from a hidden Boolean-ring or unital
assumption on the ambient sorts.

Mathlib and Track B already provide the additive pairing associated
with every finite atom matrix; reuse that result directly.
This is needed to package generated ambient substructures as genuine
finite native Folkman pairing objects.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical BigOperators

/-- The ambient pairing restricted to one finite atom stage agrees
on every element with the already established native finite
atom-matrix realisation. -/
theorem FolkmanFiniteAtomStage.pairing_eq_codeRealisation
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    (S : FolkmanFiniteAtomStage L R β)
    (a : FolkmanNativeCodeRing S.atom.leftCount)
    (b : FolkmanNativeCodeRing S.atom.rightCount) :
    β (S.left a) (S.right b) =
      (folkmanNativeCodeRealisation S.atom).pairing a b := by
  simpa only [folkmanNativeCodeRealisation,
    toBoolRing_ofBoolRing] using
      (S.preserves_pairing (ofBoolRing a) (ofBoolRing b))

/-- The original ambient pairing is additive on the left image of
every finite atom stage, without assuming an ambient unit. -/
theorem FolkmanFiniteAtomStage.pairing_add_left
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    (S : FolkmanFiniteAtomStage L R β)
    (a a' : FolkmanNativeCodeRing S.atom.leftCount)
    (b : FolkmanNativeCodeRing S.atom.rightCount) :
    β (S.left (a + a')) (S.right b) =
      β (S.left a) (S.right b) +
        β (S.left a') (S.right b) := by
  calc
    β (S.left (a + a')) (S.right b) =
        (folkmanNativeCodeRealisation S.atom).pairing (a + a') b :=
      S.pairing_eq_codeRealisation _ _
    _ = (folkmanNativeCodeRealisation S.atom).pairing a b +
        (folkmanNativeCodeRealisation S.atom).pairing a' b :=
      (folkmanNativeCodeRealisation S.atom).add_left a a' b
    _ = β (S.left a) (S.right b) +
        β (S.left a') (S.right b) := by
      rw [← S.pairing_eq_codeRealisation a b,
        ← S.pairing_eq_codeRealisation a' b]

/-- The corresponding original ambient pairing additivity on the
right image of a finite atom stage. -/
theorem FolkmanFiniteAtomStage.pairing_add_right
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    (S : FolkmanFiniteAtomStage L R β)
    (a : FolkmanNativeCodeRing S.atom.leftCount)
    (b b' : FolkmanNativeCodeRing S.atom.rightCount) :
    β (S.left a) (S.right (b + b')) =
      β (S.left a) (S.right b) +
        β (S.left a) (S.right b') := by
  calc
    β (S.left a) (S.right (b + b')) =
        (folkmanNativeCodeRealisation S.atom).pairing a (b + b') :=
      S.pairing_eq_codeRealisation _ _
    _ = (folkmanNativeCodeRealisation S.atom).pairing a b +
        (folkmanNativeCodeRealisation S.atom).pairing a b' :=
      (folkmanNativeCodeRealisation S.atom).add_right a b b'
    _ = β (S.left a) (S.right b) +
        β (S.left a) (S.right b') := by
      rw [← S.pairing_eq_codeRealisation a b,
        ← S.pairing_eq_codeRealisation a b']

/-- All ambient left pairing values are additive once every
two left elements and one right element admit one common finite
stage. This hypothesis is supplied by the directed atlas. -/
theorem FolkmanDirectedFiniteStageAtlas.pairing_add_left
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    (A : FolkmanDirectedFiniteStageAtlas L R β)
    (x x' : L) (y : R) :
    β (x + x') y = β x y + β x' y := by
  classical
  let xs : Fin 2 → L := fun i => if i = 0 then x else x'
  let ys : Fin 1 → R := fun _ => y
  let w : FolkmanFiniteTupleStageWitness (β := β) xs ys :=
    Classical.choice (A.covers 2 1 xs ys)
  let a : FolkmanNativeCodeRing w.stage.atom.leftCount :=
    toBoolRing (w.leftTuple 0)
  let a' : FolkmanNativeCodeRing w.stage.atom.leftCount :=
    toBoolRing (w.leftTuple 1)
  let b : FolkmanNativeCodeRing w.stage.atom.rightCount :=
    toBoolRing (w.rightTuple 0)
  have ha : w.stage.left a = x := by
    simpa [xs, a] using w.left_spec 0
  have ha' : w.stage.left a' = x' := by
    simpa [xs, a'] using w.left_spec 1
  have hb : w.stage.right b = y := by
    simpa [ys, b] using w.right_spec 0
  have hp := w.stage.pairing_add_left a a' b
  rw [map_add, ha, ha', hb] at hp
  exact hp

/-- Right additivity of the original ambient pairing, again derived
from finite-stage coverage rather than stipulated globally. -/
theorem FolkmanDirectedFiniteStageAtlas.pairing_add_right
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    (A : FolkmanDirectedFiniteStageAtlas L R β)
    (x : L) (y y' : R) :
    β x (y + y') = β x y + β x y' := by
  classical
  let xs : Fin 1 → L := fun _ => x
  let ys : Fin 2 → R := fun j => if j = 0 then y else y'
  let w : FolkmanFiniteTupleStageWitness (β := β) xs ys :=
    Classical.choice (A.covers 1 2 xs ys)
  let a : FolkmanNativeCodeRing w.stage.atom.leftCount :=
    toBoolRing (w.leftTuple 0)
  let b : FolkmanNativeCodeRing w.stage.atom.rightCount :=
    toBoolRing (w.rightTuple 0)
  let b' : FolkmanNativeCodeRing w.stage.atom.rightCount :=
    toBoolRing (w.rightTuple 1)
  have ha : w.stage.left a = x := by
    simpa [xs, a] using w.left_spec 0
  have hb : w.stage.right b = y := by
    simpa [ys, b] using w.right_spec 0
  have hb' : w.stage.right b' = y' := by
    simpa [ys, b'] using w.right_spec 1
  have hp := w.stage.pairing_add_right a b b'
  rw [map_add, ha, hb, hb'] at hp
  exact hp

end SuccessorTree.NonPrecompact
