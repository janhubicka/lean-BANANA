import BANANA.NonPrecompact.FolkmanFiniteHullEPPBridge

/-!
# Constructing a finite source hull from a directed stage atlas

A finite paired bridge has a finite atom-coded source ring on each
sort. We can enumerate *every* element in both source ring codes
and adjoin one prescribed new ambient element. The atlas covers
that labelled finite tuple in a single faithful finite stage.

The source maps then factor through the larger stage maps.
Injectivity of those larger maps gives unique non-unital ring
homomorphisms on the finite code, preserving both original ring
operations. Exact reconstruction of the original pairing gives the
full finite matrix condition. This is precisely the finite hull
needed in the EPP-to-one-point-bridge argument.

Both zero-ring sorts are allowed. Neither the ambient rings nor
their embeddings need to preserve a multiplicative identity.

This file is source-only pending exact-head local Lean elaboration.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical BigOperators

/-- Factor one non-unital ring homomorphism through an injective
second homomorphism whose image contains the first one's image.
The lift is genuinely a ring homomorphism, not just a pointwise
choice of preimages. No unit preservation is assumed. -/
noncomputable def folkmanNonUnitalRingHomLiftOfRange
    {A B T : Type*}
    [NonUnitalRing A] [NonUnitalRing B] [NonUnitalRing T]
    (f : A →ₙ+* T) (g : B →ₙ+* T)
    (hg : Function.Injective g)
    (h : ∀ a : A, ∃ b : B, g b = f a) :
    A →ₙ+* B := by
  classical
  let lift : A → B := fun a => Classical.choose (h a)
  have hlift (a : A) : g (lift a) = f a :=
    Classical.choose_spec (h a)
  exact {
    toFun := lift
    map_zero' := by
      apply hg
      calc
        g (lift 0) = f 0 := hlift 0
        _ = 0 := map_zero f
        _ = g 0 := (map_zero g).symm
    map_add' := by
      intro a b
      apply hg
      calc
        g (lift (a + b)) = f (a + b) := hlift _
        _ = f a + f b := map_add f a b
        _ = g (lift a) + g (lift b) := by rw [hlift a, hlift b]
        _ = g (lift a + lift b) := (map_add g _ _).symm
    map_mul' := by
      intro a b
      apply hg
      calc
        g (lift (a * b)) = f (a * b) := hlift _
        _ = f a * f b := map_mul f a b
        _ = g (lift a) * g (lift b) := by rw [hlift a, hlift b]
        _ = g (lift a * lift b) := (map_mul g _ _).symm
  }

/-- The factorisation commutes on EVERY source ring element. -/
theorem folkmanNonUnitalRingHomLiftOfRange_spec
    {A B T : Type*}
    [NonUnitalRing A] [NonUnitalRing B] [NonUnitalRing T]
    (f : A →ₙ+* T) (g : B →ₙ+* T)
    (hg : Function.Injective g)
    (h : ∀ a : A, ∃ b : B, g b = f a)
    (a : A) :
    g (folkmanNonUnitalRingHomLiftOfRange f g hg h a) = f a := by
  classical
  change g (Classical.choose (h a)) = f a
  exact Classical.choose_spec (h a)

/-- If the original map is injective, its unique lift along an
injective target stage is also injective. -/
theorem folkmanNonUnitalRingHomLiftOfRange_injective
    {A B T : Type*}
    [NonUnitalRing A] [NonUnitalRing B] [NonUnitalRing T]
    (f : A →ₙ+* T) (g : B →ₙ+* T)
    (hg : Function.Injective g)
    (h : ∀ a : A, ∃ b : B, g b = f a)
    (hf : Function.Injective f) :
    Function.Injective (folkmanNonUnitalRingHomLiftOfRange f g hg h) := by
  intro x y hxy
  apply hf
  calc
    f x = g (folkmanNonUnitalRingHomLiftOfRange f g hg h x) :=
      (folkmanNonUnitalRingHomLiftOfRange_spec f g hg h x).symm
    _ = g (folkmanNonUnitalRingHomLiftOfRange f g hg h y) :=
      congrArg g hxy
    _ = f y := folkmanNonUnitalRingHomLiftOfRange_spec f g hg h y

/-- If one genuine finite atom stage contains the full image of
both source ring maps of a paired bridge, the old code embeds
faithfully into that stage. All ring operations and full pairing
matrix values are retained. -/
noncomputable def FolkmanPairedBridgeSourceHull.of_stage
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    (P : FolkmanFinitePairedBridge L R β)
    (S : FolkmanFiniteAtomStage L R β)
    (hL : ∀ x, ∃ y, S.left y = P.source.left x)
    (hR : ∀ x, ∃ y, S.right y = P.source.right x) :
    FolkmanPairedBridgeSourceHull P := by
  classical
  let iL := folkmanNonUnitalRingHomLiftOfRange
    P.source.left S.left S.left_injective hL
  let iR := folkmanNonUnitalRingHomLiftOfRange
    P.source.right S.right S.right_injective hR
  have hcL (x) : S.left (iL x) = P.source.left x :=
    folkmanNonUnitalRingHomLiftOfRange_spec
      P.source.left S.left S.left_injective hL x
  have hcR (x) : S.right (iR x) = P.source.right x :=
    folkmanNonUnitalRingHomLiftOfRange_spec
      P.source.right S.right S.right_injective hR x
  refine {
    stage := S
    embedding := {
      left := iL
      right := iR
      left_injective :=
        folkmanNonUnitalRingHomLiftOfRange_injective
          P.source.left S.left S.left_injective hL
          P.source.left_injective
      right_injective :=
        folkmanNonUnitalRingHomLiftOfRange_injective
          P.source.right S.right S.right_injective hR
          P.source.right_injective
      pairing := ?_
    }
    left_commutes := hcL
    right_commutes := hcR
  }
  intro s t
  calc
    (∑ i ∈ ofBoolRing (iL (toBoolRing s)),
      ∑ j ∈ ofBoolRing (iR (toBoolRing t)), S.atom.edge i j) =
      β (S.left (iL (toBoolRing s)))
        (S.right (iR (toBoolRing t))) := by
          simpa only [toBoolRing_ofBoolRing] using
            (S.preserves_pairing
              (ofBoolRing (iL (toBoolRing s)))
              (ofBoolRing (iR (toBoolRing t)))).symm
    _ = β (P.source.left (toBoolRing s))
          (P.source.right (toBoolRing t)) := by
      rw [hcL, hcR]
    _ = ∑ i ∈ s, ∑ j ∈ t, P.source.atom.edge i j :=
      P.source.preserves_pairing s t

/-- The atlas itself supplies the source-LEFT finite hull
property: enumerate all elements of the old source code on
both sorts, together with the new left element x. -/
theorem FolkmanDirectedFiniteStageAtlas.sourceLeft_hull
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    (A : FolkmanDirectedFiniteStageAtlas L R β)
    (P : FolkmanFinitePairedBridge L R β) (x : L) :
    ∃ H : FolkmanPairedBridgeSourceHull P,
      ∃ a, H.stage.left a = x := by
  classical
  let LC := AsBoolRing (Finset (Fin P.source.atom.leftCount))
  let RC := AsBoolRing (Finset (Fin P.source.atom.rightCount))
  letI : Fintype LC :=
    Fintype.ofEquiv (Finset (Fin P.source.atom.leftCount)) toBoolRing
  letI : Fintype RC :=
    Fintype.ofEquiv (Finset (Fin P.source.atom.rightCount)) toBoolRing
  let eL : LC ≃ Fin (Fintype.card LC) := Fintype.equivFin LC
  let eR : RC ≃ Fin (Fintype.card RC) := Fintype.equivFin RC
  let xs : Fin (Fintype.card LC + 1) → L :=
    Fin.lastCases x (fun i => P.source.left (eL.symm i))
  let ys : Fin (Fintype.card RC) → R :=
    fun j => P.source.right (eR.symm j)
  let w : FolkmanFiniteTupleStageWitness (β := β) xs ys :=
    Classical.choice (A.covers _ _ xs ys)
  have hL : ∀ z : LC, ∃ a, w.stage.left a = P.source.left z := by
    intro z
    refine ⟨toBoolRing (w.leftTuple (Fin.castSucc (eL z))), ?_⟩
    calc
      w.stage.left (toBoolRing (w.leftTuple (Fin.castSucc (eL z)))) =
          xs (Fin.castSucc (eL z)) :=
        w.left_spec (Fin.castSucc (eL z))
      _ = P.source.left z := by
        simp [xs, eL.symm_apply_apply]
  have hR : ∀ z : RC, ∃ a, w.stage.right a = P.source.right z := by
    intro z
    refine ⟨toBoolRing (w.rightTuple (eR z)), ?_⟩
    calc
      w.stage.right (toBoolRing (w.rightTuple (eR z))) =
          ys (eR z) := w.right_spec (eR z)
      _ = P.source.right z := by simp [ys, eR.symm_apply_apply]
  let H : FolkmanPairedBridgeSourceHull P :=
    FolkmanPairedBridgeSourceHull.of_stage P w.stage hL hR
  refine ⟨H, toBoolRing (w.leftTuple (Fin.last (Fintype.card LC))), ?_⟩
  change w.stage.left
    (toBoolRing (w.leftTuple (Fin.last (Fintype.card LC)))) = x
  calc
    w.stage.left (toBoolRing (w.leftTuple (Fin.last (Fintype.card LC)))) =
      xs (Fin.last (Fintype.card LC)) :=
        w.left_spec (Fin.last (Fintype.card LC))
    _ = x := by simp [xs]

/-- The analogous source-RIGHT finite hull property is obtained
by enumerating the old source code on both sorts and adjoining
one new right element. -/
theorem FolkmanDirectedFiniteStageAtlas.sourceRight_hull
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    (A : FolkmanDirectedFiniteStageAtlas L R β)
    (P : FolkmanFinitePairedBridge L R β) (y : R) :
    ∃ H : FolkmanPairedBridgeSourceHull P,
      ∃ b, H.stage.right b = y := by
  classical
  let LC := AsBoolRing (Finset (Fin P.source.atom.leftCount))
  let RC := AsBoolRing (Finset (Fin P.source.atom.rightCount))
  letI : Fintype LC :=
    Fintype.ofEquiv (Finset (Fin P.source.atom.leftCount)) toBoolRing
  letI : Fintype RC :=
    Fintype.ofEquiv (Finset (Fin P.source.atom.rightCount)) toBoolRing
  let eL : LC ≃ Fin (Fintype.card LC) := Fintype.equivFin LC
  let eR : RC ≃ Fin (Fintype.card RC) := Fintype.equivFin RC
  let xs : Fin (Fintype.card LC) → L :=
    fun i => P.source.left (eL.symm i)
  let ys : Fin (Fintype.card RC + 1) → R :=
    Fin.lastCases y (fun j => P.source.right (eR.symm j))
  let w : FolkmanFiniteTupleStageWitness (β := β) xs ys :=
    Classical.choice (A.covers _ _ xs ys)
  have hL : ∀ z : LC, ∃ a, w.stage.left a = P.source.left z := by
    intro z
    refine ⟨toBoolRing (w.leftTuple (eL z)), ?_⟩
    calc
      w.stage.left (toBoolRing (w.leftTuple (eL z))) =
          xs (eL z) := w.left_spec (eL z)
      _ = P.source.left z := by simp [xs, eL.symm_apply_apply]
  have hR : ∀ z : RC, ∃ a, w.stage.right a = P.source.right z := by
    intro z
    refine ⟨toBoolRing (w.rightTuple (Fin.castSucc (eR z))), ?_⟩
    calc
      w.stage.right (toBoolRing (w.rightTuple (Fin.castSucc (eR z)))) =
          ys (Fin.castSucc (eR z)) :=
        w.right_spec (Fin.castSucc (eR z))
      _ = P.source.right z := by
        simp [ys, eR.symm_apply_apply]
  let H : FolkmanPairedBridgeSourceHull P :=
    FolkmanPairedBridgeSourceHull.of_stage P w.stage hL hR
  refine ⟨H, toBoolRing (w.rightTuple (Fin.last (Fintype.card RC))), ?_⟩
  change w.stage.right
    (toBoolRing (w.rightTuple (Fin.last (Fintype.card RC)))) = y
  calc
    w.stage.right (toBoolRing (w.rightTuple (Fin.last (Fintype.card RC)))) =
      ys (Fin.last (Fintype.card RC)) :=
        w.right_spec (Fin.last (Fintype.card RC))
    _ = y := by simp [ys]

/-- Every directed finite-stage atlas already has the two finite
source hull properties. No extra local-finiteness or unitality
hypothesis is needed. -/
theorem FolkmanDirectedFiniteStageAtlas.sourceHullProperty
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    (A : FolkmanDirectedFiniteStageAtlas L R β) :
    FolkmanPairedBridgeSourceHullProperty L R β where
  left := A.sourceLeft_hull
  right := A.sourceRight_hull

end SuccessorTree.NonPrecompact
