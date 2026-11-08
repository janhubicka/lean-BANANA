import BANANA.NonPrecompact.FolkmanAmbientGeneratedRingEquivs
import BANANA.NonPrecompact.FolkmanDirectedFiniteStageAtlas

/-!
# Actual ambient generated Folkman pairing isomorphisms

For two labelled ambient tuples in possibly non-unital two-sorted
rings, equality of the complete profiles of finite-stage witnesses
gives the left/right generated non-unital ring isomorphisms from
FolkmanAmbientGeneratedRingEquivs.

The missing compatibility is proved here: their restrictions send
each named generator to its partner and preserve the *original ambient*
F₂-valued pairing on every generated element.

No global ambient automorphism or ultrahomogeneity is asserted.
The proof composes actual stage-to-ambient ring maps with the finite
atom-matrix pairing preservation theorem. It never adjoins an ambient
multiplicative identity.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical BigOperators

/-- The original tuple coordinate as an element of its genuinely
non-unital generated ring. -/
def folkmanAmbientGeneratedTupleCoordinate
    {T : Type*} [NonUnitalRing T]
    {n : ℕ} (xs : Fin n → T) (i : Fin n) :
    NonUnitalSubring.closure (Set.range xs) :=
  ⟨xs i, NonUnitalSubring.subset_closure (Set.mem_range_self i)⟩

/-- The stage-generated-ring equivalence is given on elements by
the actual stage embedding into the ambient non-unital ring. -/
theorem FolkmanFiniteTupleStageWitness.left_generatedEquiv_apply
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    {nL nR : ℕ}
    {xs : Fin nL → L} {ys : Fin nR → R}
    (w : FolkmanFiniteTupleStageWitness (β := β) xs ys)
    (x : NonUnitalSubring.closure
      (Set.range (fun i => toBoolRing (w.leftTuple i)))) :
    (w.left_generatedEquiv x).val = w.stage.left x.val := by
  rfl

/-- The analogous actual evaluation of the right stage map. -/
theorem FolkmanFiniteTupleStageWitness.right_generatedEquiv_apply
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    {nL nR : ℕ}
    {xs : Fin nL → L} {ys : Fin nR → R}
    (w : FolkmanFiniteTupleStageWitness (β := β) xs ys)
    (y : NonUnitalSubring.closure
      (Set.range (fun j => toBoolRing (w.rightTuple j)))) :
    (w.right_generatedEquiv y).val = w.stage.right y.val := by
  rfl

/-- Every named left generator has the expected image under the
stage-to-ambient equivalence. -/
theorem FolkmanFiniteTupleStageWitness.left_generatedEquiv_generator
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    {nL nR : ℕ}
    {xs : Fin nL → L} {ys : Fin nR → R}
    (w : FolkmanFiniteTupleStageWitness (β := β) xs ys)
    (i : Fin nL) :
    w.left_generatedEquiv
        (folkmanGeneratedTupleCoordinate w.leftTuple i) =
      folkmanAmbientGeneratedTupleCoordinate xs i := by
  apply Subtype.ext
  calc
    (w.left_generatedEquiv
        (folkmanGeneratedTupleCoordinate w.leftTuple i)).val =
        w.stage.left
          (folkmanGeneratedTupleCoordinate w.leftTuple i).val :=
      w.left_generatedEquiv_apply _
    _ = xs i := w.left_spec i

/-- The same generator preservation on the right original sort. -/
theorem FolkmanFiniteTupleStageWitness.right_generatedEquiv_generator
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    {nL nR : ℕ}
    {xs : Fin nL → L} {ys : Fin nR → R}
    (w : FolkmanFiniteTupleStageWitness (β := β) xs ys)
    (j : Fin nR) :
    w.right_generatedEquiv
        (folkmanGeneratedTupleCoordinate w.rightTuple j) =
      folkmanAmbientGeneratedTupleCoordinate ys j := by
  apply Subtype.ext
  calc
    (w.right_generatedEquiv
        (folkmanGeneratedTupleCoordinate w.rightTuple j)).val =
        w.stage.right
          (folkmanGeneratedTupleCoordinate w.rightTuple j).val :=
      w.right_generatedEquiv_apply _
    _ = ys j := w.right_spec j

/-- A pair of isomorphisms between the actual ambient generated
non-unital subrings, preserving their named tuple elements and
all original cross-sort pairing values. -/
structure FolkmanAmbientGeneratedTwoSortIso
    {LA RA LB RB : Type*}
    [NonUnitalRing LA] [NonUnitalRing RA]
    [NonUnitalRing LB] [NonUnitalRing RB]
    (βA : LA → RA → F2) (βB : LB → RB → F2)
    {nL nR : ℕ}
    (xsA : Fin nL → LA) (ysA : Fin nR → RA)
    (xsB : Fin nL → LB) (ysB : Fin nR → RB) where
  left :
    NonUnitalSubring.closure (Set.range xsA) ≃+*
      NonUnitalSubring.closure (Set.range xsB)
  right :
    NonUnitalSubring.closure (Set.range ysA) ≃+*
      NonUnitalSubring.closure (Set.range ysB)
  left_generators : ∀ i,
    left (folkmanAmbientGeneratedTupleCoordinate xsA i) =
      folkmanAmbientGeneratedTupleCoordinate xsB i
  right_generators : ∀ j,
    right (folkmanAmbientGeneratedTupleCoordinate ysA j) =
      folkmanAmbientGeneratedTupleCoordinate ysB j
  preserves_pairing :
    ∀ (x : NonUnitalSubring.closure (Set.range xsA))
      (y : NonUnitalSubring.closure (Set.range ysA)),
      βB (left x).val (right y).val = βA x.val y.val

/-- A complete finite Folkman tuple profile determines the
isomorphism type of the *actual ambient finitely generated*
non-unital two-sort structure with its original pairing.

The finite stage maps need not preserve a greatest element,
and neither ambient ring is assumed to possess an identity.
This statement does not imply extension to a global automorphism. -/
noncomputable def folkmanAmbientGeneratedTwoSortIso_of_profile_eq
    {LA RA LB RB : Type*}
    [NonUnitalRing LA] [NonUnitalRing RA]
    [NonUnitalRing LB] [NonUnitalRing RB]
    {βA : LA → RA → F2} {βB : LB → RB → F2}
    {nL nR : ℕ}
    {xsA : Fin nL → LA} {ysA : Fin nR → RA}
    {xsB : Fin nL → LB} {ysB : Fin nR → RB}
    (w : FolkmanFiniteTupleStageWitness (β := βA) xsA ysA)
    (v : FolkmanFiniteTupleStageWitness (β := βB) xsB ysB)
    (h : w.profile = v.profile) :
    FolkmanAmbientGeneratedTwoSortIso βA βB xsA ysA xsB ysB := by
  classical
  let e : FolkmanGeneratedTwoSortIso
      w.leftTuple w.rightTuple v.leftTuple v.rightTuple :=
    folkmanGeneratedTwoSortIso_of_profile_eq
      w.leftTuple w.rightTuple v.leftTuple v.rightTuple h
  refine {
    left := w.left_generatedEquiv.symm.trans
      (e.left.trans v.left_generatedEquiv)
    right := w.right_generatedEquiv.symm.trans
      (e.right.trans v.right_generatedEquiv)
    left_generators := ?_
    right_generators := ?_
    preserves_pairing := ?_
  }
  · intro i
    have hw :
        w.left_generatedEquiv.symm
            (folkmanAmbientGeneratedTupleCoordinate xsA i) =
          folkmanGeneratedTupleCoordinate w.leftTuple i := by
      apply w.left_generatedEquiv.injective
      calc
        w.left_generatedEquiv
            (w.left_generatedEquiv.symm
              (folkmanAmbientGeneratedTupleCoordinate xsA i)) =
            folkmanAmbientGeneratedTupleCoordinate xsA i :=
          w.left_generatedEquiv.apply_symm_apply _
        _ = w.left_generatedEquiv
            (folkmanGeneratedTupleCoordinate w.leftTuple i) :=
          (w.left_generatedEquiv_generator i).symm
    change v.left_generatedEquiv
        (e.left (w.left_generatedEquiv.symm
          (folkmanAmbientGeneratedTupleCoordinate xsA i))) =
      folkmanAmbientGeneratedTupleCoordinate xsB i
    rw [hw, e.map_left_generators i,
      v.left_generatedEquiv_generator i]
  · intro j
    have hw :
        w.right_generatedEquiv.symm
            (folkmanAmbientGeneratedTupleCoordinate ysA j) =
          folkmanGeneratedTupleCoordinate w.rightTuple j := by
      apply w.right_generatedEquiv.injective
      calc
        w.right_generatedEquiv
            (w.right_generatedEquiv.symm
              (folkmanAmbientGeneratedTupleCoordinate ysA j)) =
            folkmanAmbientGeneratedTupleCoordinate ysA j :=
          w.right_generatedEquiv.apply_symm_apply _
        _ = w.right_generatedEquiv
            (folkmanGeneratedTupleCoordinate w.rightTuple j) :=
          (w.right_generatedEquiv_generator j).symm
    change v.right_generatedEquiv
        (e.right (w.right_generatedEquiv.symm
          (folkmanAmbientGeneratedTupleCoordinate ysA j))) =
      folkmanAmbientGeneratedTupleCoordinate ysB j
    rw [hw, e.map_right_generators j,
      v.right_generatedEquiv_generator j]
  · intro x y
    let a := w.left_generatedEquiv.symm x
    let b := w.right_generatedEquiv.symm y
    have hx : w.stage.left a.val = x.val := by
      calc
        w.stage.left a.val = (w.left_generatedEquiv a).val :=
          (w.left_generatedEquiv_apply a).symm
        _ = x.val := congrArg Subtype.val
          (w.left_generatedEquiv.apply_symm_apply x)
    have hy : w.stage.right b.val = y.val := by
      calc
        w.stage.right b.val = (w.right_generatedEquiv b).val :=
          (w.right_generatedEquiv_apply b).symm
        _ = y.val := congrArg Subtype.val
          (w.right_generatedEquiv.apply_symm_apply y)
    have hvx :
        (v.left_generatedEquiv (e.left a)).val =
          v.stage.left (e.left a).val :=
      v.left_generatedEquiv_apply (e.left a)
    have hvy :
        (v.right_generatedEquiv (e.right b)).val =
          v.stage.right (e.right b).val :=
      v.right_generatedEquiv_apply (e.right b)
    change βB
      (v.left_generatedEquiv (e.left a)).val
      (v.right_generatedEquiv (e.right b)).val =
        βA x.val y.val
    calc
      βB (v.left_generatedEquiv (e.left a)).val
          (v.right_generatedEquiv (e.right b)).val =
          βB (v.stage.left (e.left a).val)
            (v.stage.right (e.right b).val) := by
        rw [hvx, hvy]
      _ = (∑ i ∈ ofBoolRing (e.left a).val,
          ∑ j ∈ ofBoolRing (e.right b).val,
            v.stage.atom.edge i j) := by
        simpa only [toBoolRing_ofBoolRing] using
          (v.stage.preserves_pairing
            (ofBoolRing (e.left a).val)
            (ofBoolRing (e.right b).val))
      _ = (∑ i ∈ ofBoolRing a.val,
          ∑ j ∈ ofBoolRing b.val,
            w.stage.atom.edge i j) := e.map_pairing a b
      _ = βA (w.stage.left a.val)
          (w.stage.right b.val) := by
        simpa only [toBoolRing_ofBoolRing] using
          (w.stage.preserves_pairing
            (ofBoolRing a.val)
            (ofBoolRing b.val)).symm
      _ = βA x.val y.val := by rw [hx, hy]

end SuccessorTree.NonPrecompact
