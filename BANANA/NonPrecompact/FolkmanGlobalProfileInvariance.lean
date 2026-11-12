import BANANA.NonPrecompact.FolkmanGlobalGeneratedHomogeneity

/-!
# Genuine automorphism invariance and exact Folkman tuple profiles

A finite atom stage remains a finite atom stage after composing both
original non-unital embeddings with a global automorphism of the
original two-sorted pairing. The atom code is unchanged, and its
entire cross-pairing is preserved by the same global automorphism.

Consequently the stage-independent finite profile is invariant under
every *actual global pairing-preserving automorphism*, independently
of any homogeneity assumption. Combined with generated homogeneity,
this gives a genuine if-and-only-if orbit classification for ordered
two-sort tuple pairs and mixed-sort tuples.

The existence of the countable Folkman Fraisse limit and its
generated homogeneity are NOT proved here. They remain explicit
hypotheses of the conditional classification theorems.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical BigOperators

/-- A global pairing automorphism transports an injectively embedded
finite stage to another finite stage with the same atom matrix. -/
noncomputable def FolkmanGlobalPairAutomorphism.mapStage
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    (E : FolkmanGlobalPairAutomorphism L R β)
    (S : FolkmanFiniteAtomStage L R β) :
    FolkmanFiniteAtomStage L R β where
  atom := S.atom
  left := {
    toFun := fun x => E.left (S.left x)
    map_zero' := by
      change E.left (S.left 0) = 0
      rw [map_zero, map_zero]
    map_add' := by
      intro x y
      change E.left (S.left (x + y)) =
        E.left (S.left x) + E.left (S.left y)
      rw [map_add, map_add]
    map_mul' := by
      intro x y
      change E.left (S.left (x * y)) =
        E.left (S.left x) * E.left (S.left y)
      rw [map_mul, map_mul]
  }
  right := {
    toFun := fun y => E.right (S.right y)
    map_zero' := by
      change E.right (S.right 0) = 0
      rw [map_zero, map_zero]
    map_add' := by
      intro x y
      change E.right (S.right (x + y)) =
        E.right (S.right x) + E.right (S.right y)
      rw [map_add, map_add]
    map_mul' := by
      intro x y
      change E.right (S.right (x * y)) =
        E.right (S.right x) * E.right (S.right y)
      rw [map_mul, map_mul]
  }
  left_injective := by
    intro x y hxy
    apply S.left_injective
    apply E.left.injective
    exact hxy
  right_injective := by
    intro x y hxy
    apply S.right_injective
    apply E.right.injective
    exact hxy
  preserves_pairing := by
    intro s t
    change β (E.left (S.left (toBoolRing s)))
      (E.right (S.right (toBoolRing t))) =
      ∑ a ∈ s, ∑ b ∈ t, S.atom.edge a b
    exact (E.preserves_pairing _ _).trans
      (S.preserves_pairing s t)

/-- Transport a concrete finite-stage witness along a *global*
automorphism, with unchanged finite code and atom membership sets. -/
noncomputable def FolkmanGlobalPairAutomorphism.mapStageWitness
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    (E : FolkmanGlobalPairAutomorphism L R β)
    {nL nR : ℕ}
    {xs : Fin nL → L} {ys : Fin nR → R}
    (w : FolkmanFiniteTupleStageWitness (β := β) xs ys) :
    FolkmanFiniteTupleStageWitness (β := β)
      (fun i => E.left (xs i)) (fun j => E.right (ys j)) where
  stage := E.mapStage w.stage
  leftTuple := w.leftTuple
  rightTuple := w.rightTuple
  left_spec := by
    intro i
    change E.left (w.stage.left (toBoolRing (w.leftTuple i))) =
      E.left (xs i)
    rw [w.left_spec i]
  right_spec := by
    intro j
    change E.right (w.stage.right (toBoolRing (w.rightTuple j))) =
      E.right (ys j)
    rw [w.right_spec j]

/-- Automorphism transport changes neither the finite atom code nor
the complete profile calculated in that finite stage. -/
theorem FolkmanGlobalPairAutomorphism.mapStageWitness_profile
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    (E : FolkmanGlobalPairAutomorphism L R β)
    {nL nR : ℕ}
    {xs : Fin nL → L} {ys : Fin nR → R}
    (w : FolkmanFiniteTupleStageWitness (β := β) xs ys) :
    (E.mapStageWitness w).profile = w.profile := by
  rfl

/-- Stage-independent tuple profiles are invariant under every
genuine global pairing-preserving automorphism. No homogeneous
extension hypothesis is needed for this direction. -/
theorem FolkmanDirectedFiniteStageAtlas.tupleProfile_global_invariant
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    (A : FolkmanDirectedFiniteStageAtlas L R β)
    (E : FolkmanGlobalPairAutomorphism L R β)
    {nL nR : ℕ}
    (xs : Fin nL → L) (ys : Fin nR → R) :
    A.tupleProfile (fun i => E.left (xs i))
        (fun j => E.right (ys j)) =
      A.tupleProfile xs ys := by
  classical
  let w : FolkmanFiniteTupleStageWitness (β := β) xs ys :=
    Classical.choice (A.covers nL nR xs ys)
  calc
    A.tupleProfile (fun i => E.left (xs i))
        (fun j => E.right (ys j)) =
          (E.mapStageWitness w).profile :=
      A.tupleProfile_eq_witness
        (fun i => E.left (xs i))
        (fun j => E.right (ys j))
        (E.mapStageWitness w)
    _ = w.profile := E.mapStageWitness_profile w
    _ = A.tupleProfile xs ys :=
      (A.tupleProfile_eq_witness xs ys w).symm

/-- Actual global automorphism-orbit equivalence implies equality
of the stage-independent complete profiles. -/
theorem FolkmanDirectedFiniteStageAtlas.tupleProfile_eq_of_globalRelated
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    (A : FolkmanDirectedFiniteStageAtlas L R β)
    {nL nR : ℕ}
    (p q : (Fin nL → L) × (Fin nR → R))
    (h : folkmanGlobalTupleRelated β p q) :
    A.tupleProfile p.1 p.2 = A.tupleProfile q.1 q.2 := by
  obtain ⟨E, hL, hR⟩ := h
  have hl : (fun i => E.left (p.1 i)) = q.1 := by
    funext i
    exact hL i
  have hr : (fun j => E.right (p.2 j)) = q.2 := by
    funext j
    exact hR j
  calc
    A.tupleProfile p.1 p.2 =
        A.tupleProfile (fun i => E.left (p.1 i))
          (fun j => E.right (p.2 j)) :=
      (A.tupleProfile_global_invariant E p.1 p.2).symm
    _ = A.tupleProfile q.1 q.2 := by rw [hl, hr]

/-- True global orbit equivalence is EXACTLY equality of the
finite stage-independent tuple profiles if the ambient model
has the intrinsic generated-homogeneity property.

This does not assert that a particular countable model already
satisfies the homogeneity assumption. -/
theorem folkmanGlobalTupleRelated_iff_profile_eq
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    (A : FolkmanDirectedFiniteStageAtlas L R β)
    (hHom : FolkmanGeneratedHomogeneous L R β)
    {nL nR : ℕ}
    (p q : (Fin nL → L) × (Fin nR → R)) :
    folkmanGlobalTupleRelated β p q ↔
      A.tupleProfile p.1 p.2 = A.tupleProfile q.1 q.2 := by
  constructor
  · exact A.tupleProfile_eq_of_globalRelated p q
  · intro hp
    let w : FolkmanFiniteTupleStageWitness (β := β) p.1 p.2 :=
      Classical.choice (A.covers nL nR p.1 p.2)
    let v : FolkmanFiniteTupleStageWitness (β := β) q.1 q.2 :=
      Classical.choice (A.covers nL nR q.1 q.2)
    have hcode : w.profile = v.profile :=
      A.witnesses_profile_eq p.1 q.1 p.2 q.2 hp w v
    exact hHom p q
      (folkmanAmbientGeneratedTwoSortIso_of_profile_eq w v hcode)

/-- A global pairing automorphism does not change any sort label. -/
theorem FolkmanGlobalPairAutomorphism.mapTagged_pattern
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    (E : FolkmanGlobalPairAutomorphism L R β)
    {n : ℕ}
    (t : FolkmanTaggedStageTuple L R n) :
    folkmanTaggedStagePattern (fun i => E.mapTagged (t i)) =
      folkmanTaggedStagePattern t := by
  funext i
  cases h : t i with
  | inl x => rfl
  | inr y => rfl

/-- Masking the right sort before or after a global automorphism
agrees, because the automorphism fixes zero on the left ring. -/
theorem FolkmanGlobalPairAutomorphism.mapTagged_leftMask
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    (E : FolkmanGlobalPairAutomorphism L R β)
    {n : ℕ}
    (t : FolkmanTaggedStageTuple L R n) :
    folkmanTaggedStageLeft (fun i => E.mapTagged (t i)) =
      (fun i => E.left (folkmanTaggedStageLeft t i)) := by
  funext i
  cases h : t i with
  | inl x => rfl
  | inr y =>
      change (0 : L) = E.left 0
      exact (map_zero E.left).symm

/-- The corresponding naturality of the right-sort masking. -/
theorem FolkmanGlobalPairAutomorphism.mapTagged_rightMask
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    (E : FolkmanGlobalPairAutomorphism L R β)
    {n : ℕ}
    (t : FolkmanTaggedStageTuple L R n) :
    folkmanTaggedStageRight (fun i => E.mapTagged (t i)) =
      (fun i => E.right (folkmanTaggedStageRight t i)) := by
  funext i
  cases h : t i with
  | inl x =>
      change (0 : R) = E.right 0
      exact (map_zero E.right).symm
  | inr y => rfl

/-- The full tagged profile, including the true sort pattern, is
invariant under the action of a genuine global automorphism. -/
theorem FolkmanDirectedFiniteStageAtlas.taggedProfile_global_invariant
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    (A : FolkmanDirectedFiniteStageAtlas L R β)
    (E : FolkmanGlobalPairAutomorphism L R β)
    {n : ℕ}
    (t : FolkmanTaggedStageTuple L R n) :
    A.taggedProfile (fun i => E.mapTagged (t i)) =
      A.taggedProfile t := by
  change
    (folkmanTaggedStagePattern (fun i => E.mapTagged (t i)),
      A.tupleProfile
        (folkmanTaggedStageLeft (fun i => E.mapTagged (t i)))
        (folkmanTaggedStageRight (fun i => E.mapTagged (t i)))) =
    (folkmanTaggedStagePattern t,
      A.tupleProfile (folkmanTaggedStageLeft t)
        (folkmanTaggedStageRight t))
  rw [E.mapTagged_pattern t,
    E.mapTagged_leftMask t, E.mapTagged_rightMask t]
  exact congrArg (fun p => (folkmanTaggedStagePattern t, p))
    (A.tupleProfile_global_invariant E
      (folkmanTaggedStageLeft t) (folkmanTaggedStageRight t))

/-- Actual mixed-sort global orbit equivalence forces equality
of the complete tagged invariant, independently of homogeneity. -/
theorem FolkmanDirectedFiniteStageAtlas.taggedProfile_eq_of_globalRelated
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    (A : FolkmanDirectedFiniteStageAtlas L R β)
    {n : ℕ}
    (t u : FolkmanTaggedStageTuple L R n)
    (h : folkmanGlobalTaggedRelated β t u) :
    A.taggedProfile t = A.taggedProfile u := by
  obtain ⟨E, hmap⟩ := h
  have ht : (fun i => E.mapTagged (t i)) = u := by
    funext i
    exact hmap i
  calc
    A.taggedProfile t =
        A.taggedProfile (fun i => E.mapTagged (t i)) :=
      (A.taggedProfile_global_invariant E t).symm
    _ = A.taggedProfile u := by rw [ht]

/-- For an ambient directed Folkman atlas with generated
homogeneity, mixed-sort tuples are in the same *genuine* global
automorphism orbit exactly when their complete tagged profiles
are identical. The countable limit is not constructed here. -/
theorem folkmanGlobalTaggedRelated_iff_profile_eq
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    (A : FolkmanDirectedFiniteStageAtlas L R β)
    (hHom : FolkmanGeneratedHomogeneous L R β)
    {n : ℕ}
    (t u : FolkmanTaggedStageTuple L R n) :
    folkmanGlobalTaggedRelated β t u ↔
      A.taggedProfile t = A.taggedProfile u := by
  constructor
  · exact A.taggedProfile_eq_of_globalRelated t u
  · intro hp
    have hSort : folkmanTaggedStagePattern t =
        folkmanTaggedStagePattern u := congrArg Prod.fst hp
    have hProfile :
        A.tupleProfile (folkmanTaggedStageLeft t)
          (folkmanTaggedStageRight t) =
        A.tupleProfile (folkmanTaggedStageLeft u)
          (folkmanTaggedStageRight u) := congrArg Prod.snd hp
    have hRel : folkmanGlobalTupleRelated β
        (folkmanTaggedStageLeft t, folkmanTaggedStageRight t)
        (folkmanTaggedStageLeft u, folkmanTaggedStageRight u) :=
      (folkmanGlobalTupleRelated_iff_profile_eq A hHom _ _).mpr hProfile
    exact folkmanGlobalTaggedRelated_of_masked_tupleRelated
      t u hSort hRel

end SuccessorTree.NonPrecompact
