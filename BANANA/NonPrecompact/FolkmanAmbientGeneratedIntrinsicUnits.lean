import BANANA.NonPrecompact.FolkmanDirectedFiniteLocalFiniteness
import BANANA.NonPrecompact.FolkmanNativeFiniteHeredity

/-!
# Intrinsic Boolean-ring units in generated substructures of a non-unital limit

The intended countable Folkman limit is only a NonUnitalRing: its
ambient ring sorts need not possess a unit. Track B's finite
heredity theorem, however, takes a NonUnitalSubring of a BooleanRing
as input and constructs the subring's intrinsic identity.

The correct bridge is to apply Track B *inside a finite atom stage*,
where the full powerset carrier is a BooleanRing, then transport the
resulting BooleanRing structure to the actual ambient generated
subring using the existing stage-to-ambient RingEquiv.

No global ambient one is introduced. These are definitions of local
structures, NOT typeclass instances and NOT a claim that the entire
ambient ring is unital.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical

/-- A Boolean ring structure transfers across a non-unital ring
equivalence. The target need not possess any previously named
multiplicative identity; it receives precisely the image of
the source ring's unit. -/
noncomputable def folkmanBooleanRingOfNonUnitalEquiv
    {S T : Type*} [BooleanRing S] [NonUnitalRing T]
    (e : S ≃+* T) : BooleanRing T where
  __ := (inferInstance : NonUnitalRing T)
  one := e (1 : S)
  one_mul := by
    intro x
    calc
      e (1 : S) * x =
          e (1 : S) * e (e.symm x) := by
        rw [e.apply_symm_apply]
      _ = e ((1 : S) * e.symm x) :=
        (e.map_mul _ _).symm
      _ = e (e.symm x) := by
        rw [one_mul]
      _ = x := e.apply_symm_apply x
  mul_one := by
    intro x
    calc
      x * e (1 : S) =
          e (e.symm x) * e (1 : S) := by
        rw [e.apply_symm_apply]
      _ = e (e.symm x * (1 : S)) :=
        (e.map_mul _ _).symm
      _ = e (e.symm x) := by
        rw [mul_one]
      _ = x := e.apply_symm_apply x
  isIdempotentElem x := by
    change x * x = x
    calc
      x * x = e (e.symm x) * e (e.symm x) := by
        rw [e.apply_symm_apply]
      _ = e (e.symm x * e.symm x) :=
        (e.map_mul _ _).symm
      _ = e (e.symm x) := by
        rw [BooleanRing.mul_self]
      _ = x := e.apply_symm_apply x

/-- The actual ambient left generated subring of a finite stage
witness is a finite Boolean ring with its own intrinsic unit,
even if the ambient left sort has no multiplicative identity.

The BooleanRing structure is transported from the generated
subring of the finite powerset stage; no unitality of the stage
embedding is required. -/
noncomputable def FolkmanFiniteTupleStageWitness.left_generatedBooleanRing
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    {nL nR : ℕ}
    {xs : Fin nL → L} {ys : Fin nR → R}
    (w : FolkmanFiniteTupleStageWitness (β := β) xs ys) :
    BooleanRing (NonUnitalSubring.closure (Set.range xs)) := by
  classical
  let S : NonUnitalSubring
      (AsBoolRing (Finset (Fin w.stage.atom.leftCount))) :=
    NonUnitalSubring.closure
      (Set.range (fun i => toBoolRing (w.leftTuple i)))
  letI : Fintype
      (AsBoolRing (Finset (Fin w.stage.atom.leftCount))) :=
    Fintype.ofEquiv (Finset (Fin w.stage.atom.leftCount)) toBoolRing
  letI : Fintype S := Fintype.ofFinite S
  letI : BooleanRing S := folkmanNativeSubringBooleanRing S
  exact folkmanBooleanRingOfNonUnitalEquiv w.left_generatedEquiv

/-- The right generated subring likewise has its own Boolean-ring
identity, independent of any ambient ring identity. -/
noncomputable def FolkmanFiniteTupleStageWitness.right_generatedBooleanRing
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    {nL nR : ℕ}
    {xs : Fin nL → L} {ys : Fin nR → R}
    (w : FolkmanFiniteTupleStageWitness (β := β) xs ys) :
    BooleanRing (NonUnitalSubring.closure (Set.range ys)) := by
  classical
  let S : NonUnitalSubring
      (AsBoolRing (Finset (Fin w.stage.atom.rightCount))) :=
    NonUnitalSubring.closure
      (Set.range (fun j => toBoolRing (w.rightTuple j)))
  letI : Fintype
      (AsBoolRing (Finset (Fin w.stage.atom.rightCount))) :=
    Fintype.ofEquiv (Finset (Fin w.stage.atom.rightCount)) toBoolRing
  letI : Fintype S := Fintype.ofFinite S
  letI : BooleanRing S := folkmanNativeSubringBooleanRing S
  exact folkmanBooleanRingOfNonUnitalEquiv w.right_generatedEquiv

end SuccessorTree.NonPrecompact
