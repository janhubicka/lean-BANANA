import BANANA.NonPrecompact.FolkmanDirectedFiniteStageAtlas
import BANANA.NonPrecompact.FolkmanFiniteProfileOrbitCriterion
import BANANA.NonPrecompact.FolkmanGeneratedTwoSortProfileIso

/-!
# From stage-independent Folkman profiles to finite global orbits

This file connects three already separate finite statements:
(1) a tuple in a directed finite-stage atlas has a choice-independent
complete profile; (2) equal profiles yield an isomorphism of the
two finite generated non-unital structures; (3) a complete invariant
of finite type has a finite orbit quotient.

The missing *infinite* hypothesis is stated openly: a
generator-preserving isomorphism of the two finite generated structures
must extend to a global pairing-preserving automorphism, hence to
an orbit of the actual automorphism action. No such action or
extension theorem is constructed here.

The mixed-sort version records which coordinates belong to each sort.
-/

namespace SuccessorTree.NonPrecompact

/-- If two ambient tuple pairs have the same atlas profile, all their
finite stage witnesses have the same complete profile. -/
theorem FolkmanDirectedFiniteStageAtlas.witnesses_profile_eq
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    (A : FolkmanDirectedFiniteStageAtlas L R β)
    {nL nR : ℕ}
    (xs xs' : Fin nL → L) (ys ys' : Fin nR → R)
    (h : A.tupleProfile xs ys = A.tupleProfile xs' ys')
    (w : FolkmanFiniteTupleStageWitness (β := β) xs ys)
    (v : FolkmanFiniteTupleStageWitness (β := β) xs' ys') :
    w.profile = v.profile := by
  calc
    w.profile = A.tupleProfile xs ys :=
      (A.tupleProfile_eq_witness xs ys w).symm
    _ = A.tupleProfile xs' ys' := h
    _ = v.profile := A.tupleProfile_eq_witness xs' ys' v

/-- A *conditional* genuine global-orbit bound for two ordered tuples.
The group action is supplied externally, and hhom explicitly asserts
that each finite-generated-structure isomorphism yields an element of
the corresponding global orbit. This must eventually be discharged
by ultrahomogeneity of the actual countable Folkman limit. -/
theorem folkmanDirectedFiniteStageAtlas_orbits_finite_of_homogeneity
    {L R G : Type*} [NonUnitalRing L] [NonUnitalRing R]
    [Group G]
    {β : L → R → F2}
    (A : FolkmanDirectedFiniteStageAtlas L R β)
    (nL nR : ℕ)
    [MulAction G ((Fin nL → L) × (Fin nR → R))]
    (hhom :
      ∀ (p q : (Fin nL → L) × (Fin nR → R))
        (w : FolkmanFiniteTupleStageWitness (β := β) p.1 p.2)
        (v : FolkmanFiniteTupleStageWitness (β := β) q.1 q.2),
        FolkmanGeneratedTwoSortIso w.leftTuple w.rightTuple
          v.leftTuple v.rightTuple →
          p ∈ MulAction.orbit G q) :
    Finite (MulAction.orbitRel.Quotient G
      ((Fin nL → L) × (Fin nR → R))) := by
  classical
  apply folkmanFiniteProfile_orbits_finite nL nR
    (fun p : (Fin nL → L) × (Fin nR → R) =>
      A.tupleProfile p.1 p.2)
  intro p q hp
  let w : FolkmanFiniteTupleStageWitness (β := β) p.1 p.2 :=
    Classical.choice (A.covers nL nR p.1 p.2)
  let v : FolkmanFiniteTupleStageWitness (β := β) q.1 q.2 :=
    Classical.choice (A.covers nL nR q.1 q.2)
  have hfinite : w.profile = v.profile :=
    A.witnesses_profile_eq p.1 q.1 p.2 q.2 hp w v
  let e : FolkmanGeneratedTwoSortIso
      w.leftTuple w.rightTuple v.leftTuple v.rightTuple :=
    folkmanGeneratedTwoSortIso_of_profile_eq
      w.leftTuple w.rightTuple v.leftTuple v.rightTuple hfinite
  exact hhom p q w v e

/-- A finite tuple in the disjoint union of the two ambient sorts. -/
abbrev FolkmanTaggedStageTuple (L R : Type*) (n : ℕ) :=
  Fin n → Sum L R

/-- The true sort of each coordinate is part of the invariant. -/
def folkmanTaggedStagePattern
    {L R : Type*} {n : ℕ}
    (t : FolkmanTaggedStageTuple L R n) : Fin n → Bool :=
  fun i => match t i with
    | .inl _ => true
    | .inr _ => false

/-- Mask right-sort coordinates with the left zero. -/
def folkmanTaggedStageLeft
    {L R : Type*} [Zero L] {n : ℕ}
    (t : FolkmanTaggedStageTuple L R n) : Fin n → L :=
  fun i => match t i with
    | .inl x => x
    | .inr _ => 0

/-- Mask left-sort coordinates with the right zero. -/
def folkmanTaggedStageRight
    {L R : Type*} [Zero R] {n : ℕ}
    (t : FolkmanTaggedStageTuple L R n) : Fin n → R :=
  fun i => match t i with
    | .inl _ => 0
    | .inr y => y

/-- One finite invariant of an arbitrary mixed-sort tuple: the
coordinate-sort pattern together with the complete two-sort profile
of the masked left and right tuples. -/
noncomputable def FolkmanDirectedFiniteStageAtlas.taggedProfile
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    (A : FolkmanDirectedFiniteStageAtlas L R β)
    {n : ℕ} (t : FolkmanTaggedStageTuple L R n) :
    FolkmanTaggedFiniteProfile n :=
  (folkmanTaggedStagePattern t,
    A.tupleProfile (folkmanTaggedStageLeft t)
      (folkmanTaggedStageRight t))

/-- A conditional *mixed-sort* oligomorphicity criterion.
The homogeneous extension condition is stated for actual tagged
tuples and never inferred solely from finite stage invariance. -/
theorem folkmanDirectedFiniteStageAtlas_taggedOrbits_finite_of_homogeneity
    {L R G : Type*} [NonUnitalRing L] [NonUnitalRing R]
    [Group G]
    {β : L → R → F2}
    (A : FolkmanDirectedFiniteStageAtlas L R β)
    (n : ℕ)
    [MulAction G (FolkmanTaggedStageTuple L R n)]
    (hhom :
      ∀ (t u : FolkmanTaggedStageTuple L R n)
        (w : FolkmanFiniteTupleStageWitness (β := β)
          (folkmanTaggedStageLeft t) (folkmanTaggedStageRight t))
        (v : FolkmanFiniteTupleStageWitness (β := β)
          (folkmanTaggedStageLeft u) (folkmanTaggedStageRight u)),
        folkmanTaggedStagePattern t = folkmanTaggedStagePattern u →
        FolkmanGeneratedTwoSortIso w.leftTuple w.rightTuple
          v.leftTuple v.rightTuple →
          t ∈ MulAction.orbit G u) :
    Finite (MulAction.orbitRel.Quotient G
      (FolkmanTaggedStageTuple L R n)) := by
  classical
  apply folkmanTaggedFiniteProfile_orbits_finite n A.taggedProfile
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
