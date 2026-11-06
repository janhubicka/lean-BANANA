import BANANA.NonPrecompact.FolkmanGlobalPairAutomorphismOrbits

/-!
# Genuine global automorphism orbits on mixed-sort Folkman tuples

The sort labels are part of the finite invariant. The orbit
relation uses one actual global pairing-preserving automorphism
on both sorts, not independent finite partial maps or an unrelated
group action. The finite quotient theorem is conditional on the
explicit global homogeneity/extension property of the ambient model.
-/

namespace SuccessorTree.NonPrecompact

/-- Action of a genuine global pairing automorphism on an element
of the disjoint union of the two original ring sorts. -/
def FolkmanGlobalPairAutomorphism.mapTagged
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    (E : FolkmanGlobalPairAutomorphism L R β) :
    Sum L R → Sum L R
  | .inl x => .inl (E.left x)
  | .inr y => .inr (E.right y)

/-- The tag action of the inverse undoes the original tag action. -/
theorem FolkmanGlobalPairAutomorphism.mapTagged_symm
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    (E : FolkmanGlobalPairAutomorphism L R β)
    (v : Sum L R) :
    E.symm.mapTagged (E.mapTagged v) = v := by
  cases v with
  | inl x => simp [mapTagged]
  | inr y => simp [mapTagged]

/-- The tag action agrees with composition on both sorts. -/
theorem FolkmanGlobalPairAutomorphism.mapTagged_trans
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    (E F : FolkmanGlobalPairAutomorphism L R β)
    (v : Sum L R) :
    (E.trans F).mapTagged v = F.mapTagged (E.mapTagged v) := by
  cases v with
  | inl x => rfl
  | inr y => rfl

/-- Two tagged tuples are in one orbit of the actual global
automorphism group of the two-sorted non-unital pairing. -/
def folkmanGlobalTaggedRelated
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    (β : L → R → F2) {n : ℕ}
    (t u : FolkmanTaggedStageTuple L R n) : Prop :=
  ∃ E : FolkmanGlobalPairAutomorphism L R β,
    ∀ i, E.mapTagged (t i) = u i

/-- Actual global automorphism equivalence for arbitrary mixed-sort
tuples (including tuples entirely contained in one sort). -/
def folkmanGlobalTaggedSetoid
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    (β : L → R → F2) (n : ℕ) :
    Setoid (FolkmanTaggedStageTuple L R n) where
  r := folkmanGlobalTaggedRelated β
  iseqv := by
    constructor
    · intro t
      refine ⟨FolkmanGlobalPairAutomorphism.refl β, ?_⟩
      intro i
      cases h : t i with
      | inl x => rfl
      | inr y => rfl
    · intro t u h
      obtain ⟨E, hE⟩ := h
      refine ⟨E.symm, ?_⟩
      intro i
      calc
        E.symm.mapTagged (u i) =
            E.symm.mapTagged (E.mapTagged (t i)) := by
          rw [hE i]
        _ = t i := E.mapTagged_symm (t i)
    · intro t u v htu huv
      obtain ⟨E, hE⟩ := htu
      obtain ⟨F, hF⟩ := huv
      refine ⟨E.trans F, ?_⟩
      intro i
      calc
        (E.trans F).mapTagged (t i) =
            F.mapTagged (E.mapTagged (t i)) :=
          E.mapTagged_trans F (t i)
        _ = F.mapTagged (u i) := by rw [hE i]
        _ = v i := hF i

/-- Conditional finite number of genuine global automorphism orbits
on arbitrary mixed-sort tuples. The ultrahomogeneity hypothesis is
stated for actual finite generated non-unital structures and is not
deduced merely from a finite profile. -/
theorem folkmanGlobalTaggedOrbits_finite_of_finiteHomogeneity
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    (A : FolkmanDirectedFiniteStageAtlas L R β)
    (n : ℕ)
    (hhom :
      ∀ (t u : FolkmanTaggedStageTuple L R n)
        (w : FolkmanFiniteTupleStageWitness (β := β)
          (folkmanTaggedStageLeft t) (folkmanTaggedStageRight t))
        (v : FolkmanFiniteTupleStageWitness (β := β)
          (folkmanTaggedStageLeft u) (folkmanTaggedStageRight u)),
        folkmanTaggedStagePattern t = folkmanTaggedStagePattern u →
        FolkmanGeneratedTwoSortIso w.leftTuple w.rightTuple
          v.leftTuple v.rightTuple →
          folkmanGlobalTaggedRelated β t u) :
    Finite (Quotient (folkmanGlobalTaggedSetoid β n)) := by
  classical
  letI : Setoid (FolkmanTaggedStageTuple L R n) :=
    folkmanGlobalTaggedSetoid β n
  letI : Finite (FolkmanTaggedFiniteProfile n) :=
    folkmanTaggedFiniteProfile_finite n
  apply finiteQuotient_of_completeFiniteInvariant
    (fun t : FolkmanTaggedStageTuple L R n => A.taggedProfile t)
  intro t u hp
  have hsort : folkmanTaggedStagePattern t =
      folkmanTaggedStagePattern u :=
    congrArg Prod.fst hp
  have hprofile :
      A.tupleProfile (folkmanTaggedStageLeft t)
        (folkmanTaggedStageRight t) =
      A.tupleProfile (folkmanTaggedStageLeft u)
        (folkmanTaggedStageRight u) :=
    congrArg Prod.snd hp
  let w : FolkmanFiniteTupleStageWitness (β := β)
      (folkmanTaggedStageLeft t) (folkmanTaggedStageRight t) :=
    Classical.choice (A.covers n n
      (folkmanTaggedStageLeft t) (folkmanTaggedStageRight t))
  let v : FolkmanFiniteTupleStageWitness (β := β)
      (folkmanTaggedStageLeft u) (folkmanTaggedStageRight u) :=
    Classical.choice (A.covers n n
      (folkmanTaggedStageLeft u) (folkmanTaggedStageRight u))
  have hfinite : w.profile = v.profile :=
    A.witnesses_profile_eq
      (folkmanTaggedStageLeft t) (folkmanTaggedStageLeft u)
      (folkmanTaggedStageRight t) (folkmanTaggedStageRight u)
      hprofile w v
  let e : FolkmanGeneratedTwoSortIso
      w.leftTuple w.rightTuple v.leftTuple v.rightTuple :=
    folkmanGeneratedTwoSortIso_of_profile_eq
      w.leftTuple w.rightTuple v.leftTuple v.rightTuple hfinite
  exact hhom t u w v hsort e

end SuccessorTree.NonPrecompact
