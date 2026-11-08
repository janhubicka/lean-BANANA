import BANANA.NonPrecompact.FolkmanDirectedFinitePairingLaws
import BANANA.NonPrecompact.FolkmanAmbientGeneratedIntrinsicUnits

/-!
# Finitely generated original ambient substructures are native Folkman objects

The countable ambient sorts may only carry NonUnitalRing structures,
with no global multiplicative identities. Finite-stage coverage
provides an intrinsic Boolean-ring identity on every generated
non-unital subring, and finite-stage pairing reconstruction proves
that the ORIGINAL ambient F₂ pairing is biadditive on both sorts.

Together these make each finite generated two-sort substructure
a genuine native finite Folkman object, in the exact original
language, with its own intrinsic units. This is the missing
hereditary-object interface for the initial-bridge construction.

No global ambient unit, countable limit existence or homogeneity
is assumed. Exact-head Lean verification remains outstanding.
-/

namespace SuccessorTree.NonPrecompact

/-- Package the actual ambient pairing restricted to two finitely
generated non-unital subrings as a native finite Folkman pairing.
The local BooleanRing instances come from the finite-stage
equivalences; they are NOT instances on the whole ambient rings. -/
noncomputable def FolkmanFiniteTupleStageWitness.generatedNativePairing
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    (A : FolkmanDirectedFiniteStageAtlas L R β)
    {nL nR : ℕ}
    {xs : Fin nL → L} {ys : Fin nR → R}
    (w : FolkmanFiniteTupleStageWitness (β := β) xs ys) :
    letI := w.left_generatedBooleanRing
    letI := w.right_generatedBooleanRing
    FolkmanNativeFinitePairing
      (NonUnitalSubring.closure (Set.range xs))
      (NonUnitalSubring.closure (Set.range ys)) := by
  letI : BooleanRing (NonUnitalSubring.closure (Set.range xs)) :=
    w.left_generatedBooleanRing
  letI : BooleanRing (NonUnitalSubring.closure (Set.range ys)) :=
    w.right_generatedBooleanRing
  exact {
    pairing := fun x y => β x.val y.val
    add_left := by
      intro x x' y
      change β (x.val + x'.val) y.val =
        β x.val y.val + β x'.val y.val
      exact A.pairing_add_left x.val x'.val y.val
    add_right := by
      intro x y y'
      change β x.val (y.val + y'.val) =
        β x.val y.val + β x.val y'.val
      exact A.pairing_add_right x.val y.val y'.val
  }

/-- A generated two-sort substructure from a finite stage has
finite carriers on both sides. The pairing above therefore
qualifies as a finite native Folkman object in the precise
non-unital embedding language, with no ambient unit inserted. -/
theorem FolkmanFiniteTupleStageWitness.generatedNativePairing_finite
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    (A : FolkmanDirectedFiniteStageAtlas L R β)
    {nL nR : ℕ}
    {xs : Fin nL → L} {ys : Fin nR → R}
    (w : FolkmanFiniteTupleStageWitness (β := β) xs ys) :
    Finite (NonUnitalSubring.closure (Set.range xs)) ∧
      Finite (NonUnitalSubring.closure (Set.range ys)) :=
  ⟨w.left_generated_finite, w.right_generated_finite⟩

end SuccessorTree.NonPrecompact
