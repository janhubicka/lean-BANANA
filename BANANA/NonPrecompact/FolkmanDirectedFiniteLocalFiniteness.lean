import BANANA.NonPrecompact.FolkmanDirectedFiniteStageAtlas
import Mathlib.RingTheory.NonUnitalSubring.Basic

/-!
# Local finiteness from finite non-unital Folkman stage coverage

The ambient two-sort ring need not possess a multiplicative identity.
A finite tuple whose coordinates lie in the image of any *finite*
non-unital ring homomorphism generates a finite non-unital subring:
its closure is contained in the finite range of that map.

This generic argument avoids assuming a BooleanRing instance on
an ambient unital ring or invoking Subring.closure, which would
incorrectly add the ambient unit.

It proves a necessary local-finiteness consequence of an explicitly
supplied directed finite-stage atlas. It does not construct the
Fraisse limit, and uses no global homogeneity hypothesis.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical

/-- A finite ring-map image bounds the non-unital subring generated
by a tuple lying inside that image. No injectivity, Boolean-ring
hypothesis or preservation of the ambient unit is needed. -/
theorem finite_nonunitalClosure_of_factor_through_finite
    {S T : Type*} [NonUnitalRing S] [NonUnitalRing T]
    [Fintype S]
    (f : S →ₙ+* T)
    {n : ℕ} (xs : Fin n → T)
    (hxs : ∀ i, xs i ∈ f.range) :
    Finite (NonUnitalSubring.closure (Set.range xs)) := by
  classical
  letI : Fintype f.range := NonUnitalRingHom.fintypeRange f
  have hle :
      NonUnitalSubring.closure (Set.range xs) ≤ f.range := by
    apply NonUnitalSubring.closure_le.mpr
    rintro x ⟨i, rfl⟩
    exact hxs i
  let j : NonUnitalSubring.closure (Set.range xs) → f.range :=
    fun x => ⟨x.val, hle x.property⟩
  have hj : Function.Injective j := by
    intro x y h
    apply Subtype.ext
    exact congrArg Subtype.val h
  exact Finite.of_injective j hj

/-- In an ambient non-unital left-sort ring, any tuple with a
faithful finite Folkman atom-stage witness generates a finite
non-unital subring. This includes the empty tuple and the zero
stage. -/
theorem FolkmanFiniteTupleStageWitness.left_generated_finite
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    {nL nR : ℕ} {xs : Fin nL → L} {ys : Fin nR → R}
    (w : FolkmanFiniteTupleStageWitness (β := β) xs ys) :
    Finite (NonUnitalSubring.closure (Set.range xs)) := by
  classical
  letI : Fintype
      (AsBoolRing (Finset (Fin w.stage.atom.leftCount))) :=
    Fintype.ofEquiv (Finset (Fin w.stage.atom.leftCount)) toBoolRing
  apply finite_nonunitalClosure_of_factor_through_finite
    w.stage.left xs
  intro i
  exact NonUnitalRingHom.mem_range.mpr
    ⟨toBoolRing (w.leftTuple i), w.left_spec i⟩

/-- Identical local-finiteness result for the other original sort. -/
theorem FolkmanFiniteTupleStageWitness.right_generated_finite
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    {nL nR : ℕ} {xs : Fin nL → L} {ys : Fin nR → R}
    (w : FolkmanFiniteTupleStageWitness (β := β) xs ys) :
    Finite (NonUnitalSubring.closure (Set.range ys)) := by
  classical
  letI : Fintype
      (AsBoolRing (Finset (Fin w.stage.atom.rightCount))) :=
    Fintype.ofEquiv (Finset (Fin w.stage.atom.rightCount)) toBoolRing
  apply finite_nonunitalClosure_of_factor_through_finite
    w.stage.right ys
  intro j
  exact NonUnitalRingHom.mem_range.mpr
    ⟨toBoolRing (w.rightTuple j), w.right_spec j⟩

/-- An atlas covering every finite tuple ensures local finiteness
of *both* ambient non-unital ring sorts. No common-refinement or
homogeneity assumption is needed for this consequence. -/
theorem FolkmanDirectedFiniteStageAtlas.generated_sorts_finite
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    (A : FolkmanDirectedFiniteStageAtlas L R β)
    {nL nR : ℕ} (xs : Fin nL → L) (ys : Fin nR → R) :
    Finite (NonUnitalSubring.closure (Set.range xs)) ∧
      Finite (NonUnitalSubring.closure (Set.range ys)) := by
  classical
  let w : FolkmanFiniteTupleStageWitness (β := β) xs ys :=
    Classical.choice (A.covers nL nR xs ys)
  exact ⟨w.left_generated_finite, w.right_generated_finite⟩

end SuccessorTree.NonPrecompact
