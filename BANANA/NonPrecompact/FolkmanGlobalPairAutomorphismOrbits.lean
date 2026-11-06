import BANANA.NonPrecompact.FolkmanDirectedFiniteOrbitBridge

/-!
# Genuine global non-unital Folkman pairing automorphism orbits

A global two-sort automorphism is a pair of non-unital ring
equivalences which preserves the actual cross-pairing on every
element. A finite-profile argument alone cannot produce such
automorphisms. The required extension from finite generated
substructure isomorphisms remains an explicit hypothesis.

This module uses the actual pairing-automorphism orbit equivalence,
not an arbitrary, unrelated group action. It does not construct
the countable Folkman Fraisse limit or its ultrahomogeneity.
-/

namespace SuccessorTree.NonPrecompact

/-- A genuine global automorphism of the original non-unital
two-sorted ring pairing. No unit is assumed in either sort. -/
structure FolkmanGlobalPairAutomorphism
    (L R : Type*) [NonUnitalRing L] [NonUnitalRing R]
    (β : L → R → F2) where
  left : L ≃+* L
  right : R ≃+* R
  preserves_pairing : ∀ x y, β (left x) (right y) = β x y

/-- The identity automorphism preserves the entire pairing. -/
def FolkmanGlobalPairAutomorphism.refl
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    (β : L → R → F2) :
    FolkmanGlobalPairAutomorphism L R β where
  left := RingEquiv.refl L
  right := RingEquiv.refl R
  preserves_pairing := by
    intro x y
    rfl

/-- Inverting a pairing automorphism preserves the pairing. -/
def FolkmanGlobalPairAutomorphism.symm
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    (E : FolkmanGlobalPairAutomorphism L R β) :
    FolkmanGlobalPairAutomorphism L R β where
  left := E.left.symm
  right := E.right.symm
  preserves_pairing := by
    intro x y
    have h := E.preserves_pairing (E.left.symm x) (E.right.symm y)
    simpa using h.symm

/-- Composition of pairing-preserving automorphisms. -/
def FolkmanGlobalPairAutomorphism.trans
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    (E F : FolkmanGlobalPairAutomorphism L R β) :
    FolkmanGlobalPairAutomorphism L R β where
  left := E.left.trans F.left
  right := E.right.trans F.right
  preserves_pairing := by
    intro x y
    change β (F.left (E.left x)) (F.right (E.right y)) = β x y
    exact (F.preserves_pairing (E.left x) (E.right y)).trans
      (E.preserves_pairing x y)

/-- The true orbit relation on ordered tuple pairs: a single global
two-sorted pairing-preserving ring automorphism sends p to q. -/
def folkmanGlobalTupleRelated
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    (β : L → R → F2)
    {nL nR : ℕ}
    (p q : (Fin nL → L) × (Fin nR → R)) : Prop :=
  ∃ E : FolkmanGlobalPairAutomorphism L R β,
    (∀ i, E.left (p.1 i) = q.1 i) ∧
    (∀ j, E.right (p.2 j) = q.2 j)

/-- Global pairing automorphisms define an equivalence relation.
This is genuine global-orbit equivalence, not mere isomorphism of
two finite generated substructures. -/
def folkmanGlobalTupleSetoid
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    (β : L → R → F2) (nL nR : ℕ) :
    Setoid ((Fin nL → L) × (Fin nR → R)) where
  r := folkmanGlobalTupleRelated β
  iseqv := by
    constructor
    · intro p
      refine ⟨FolkmanGlobalPairAutomorphism.refl β, ?_, ?_⟩
      · intro i
        rfl
      · intro j
        rfl
    · intro p q h
      obtain ⟨E, hL, hR⟩ := h
      refine ⟨E.symm, ?_, ?_⟩
      · intro i
        simpa using (congrArg E.left.symm (hL i)).symm
      · intro j
        simpa using (congrArg E.right.symm (hR j)).symm
    · intro p q r hpq hqr
      obtain ⟨E, hEL, hER⟩ := hpq
      obtain ⟨F, hFL, hFR⟩ := hqr
      refine ⟨E.trans F, ?_, ?_⟩
      · intro i
        change F.left (E.left (p.1 i)) = r.1 i
        rw [hEL i, hFL i]
      · intro j
        change F.right (E.right (p.2 j)) = r.2 j
        rw [hER j, hFR j]

/-- Conditional finiteness of *actual* global automorphism orbits.
The sole infinite hypothesis says that each finite generated
isomorphism obtained from a pair of stage witnesses extends to
an actual pairing-preserving global ring automorphism.

This is an interface for a future homogeneous countable limit; it
is not a theorem asserting that the unconstructed limit is
already homogeneous. -/
theorem folkmanGlobalTupleOrbits_finite_of_finiteHomogeneity
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    (A : FolkmanDirectedFiniteStageAtlas L R β)
    (nL nR : ℕ)
    (hhom :
      ∀ (p q : (Fin nL → L) × (Fin nR → R))
        (w : FolkmanFiniteTupleStageWitness (β := β) p.1 p.2)
        (v : FolkmanFiniteTupleStageWitness (β := β) q.1 q.2),
        FolkmanGeneratedTwoSortIso w.leftTuple w.rightTuple
          v.leftTuple v.rightTuple →
          folkmanGlobalTupleRelated β p q) :
    Finite (Quotient (folkmanGlobalTupleSetoid β nL nR)) := by
  classical
  letI : Setoid ((Fin nL → L) × (Fin nR → R)) :=
    folkmanGlobalTupleSetoid β nL nR
  apply folkmanFiniteProfile_quotient_finite nL nR
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

end SuccessorTree.NonPrecompact
