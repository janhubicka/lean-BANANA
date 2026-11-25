import BANANA.NonPrecompact.FolkmanNativePairing
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Native atom codes for Folkman–BANANA

The two finite atom sets and their cross-pairing matrix determine actual
finite Boolean-ring representatives. This algebraic presentation is
independent of Ramsey colourings and strong amalgamation constructions.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical symmDiff BigOperators

/-- A finite Folkman--BANANA structure in atom coordinates. -/
structure FolkmanAtomStructure where
  leftCount : ℕ
  rightCount : ℕ
  edge : Fin leftCount → Fin rightCount → ZMod 2

/-- An actual finite Boolean ring on the subsets of `Fin n`.
For `n = 0` this is the one-element zero ring. -/
abbrev FolkmanNativeCodeRing (n : ℕ) := AsBoolRing (Finset (Fin n))

noncomputable instance folkmanNativeCodeRingFintype (n : ℕ) :
    Fintype (FolkmanNativeCodeRing n) :=
  Fintype.ofEquiv (Finset (Fin n)) toBoolRing

/-- Finite sums into F₂ are additive under symmetric difference.
The intersection contributions cancel, including for empty atom types. -/
theorem folkmanNativeCode_sum_symmDiff
    {I : Type*} [Fintype I] [DecidableEq I]
    (w : I → ZMod 2) (s t : Finset I) :
    (∑ i ∈ symmDiff s t, w i) =
      (∑ i ∈ s, w i) + ∑ i ∈ t, w i := by
  classical
  have hdouble : ∀ z : ZMod 2, z + z = 0 := by decide
  have hsum (u : Finset I) :
      (∑ i ∈ u, w i) = ∑ i : I, if i ∈ u then w i else 0 := by
    have hu : Finset.univ.filter (fun i : I => i ∈ u) = u := by
      ext i
      simp
    calc
      (∑ i ∈ u, w i) =
          ∑ i ∈ Finset.univ.filter (fun i : I => i ∈ u), w i := by
            rw [hu]
      _ = ∑ i : I, if i ∈ u then w i else 0 := by
        rw [Finset.sum_filter]
  rw [hsum (symmDiff s t), hsum s, hsum t, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;>
    simp [Finset.mem_symmDiff, hs, ht, hdouble]

/-- Realise any atom matrix as a bilinear pairing on two native finite
Boolean rings. Both sorts may be zero rings. -/
noncomputable def folkmanNativeCodeRealisation (A : FolkmanAtomStructure) :
    FolkmanNativeFinitePairing
      (FolkmanNativeCodeRing A.leftCount)
      (FolkmanNativeCodeRing A.rightCount) where
  pairing := fun x y => ∑ i ∈ ofBoolRing x, ∑ j ∈ ofBoolRing y, A.edge i j
  add_left := by
    intro x x' y
    change (∑ i ∈ symmDiff (ofBoolRing x) (ofBoolRing x'),
        ∑ j ∈ ofBoolRing y, A.edge i j) =
      (∑ i ∈ ofBoolRing x, ∑ j ∈ ofBoolRing y, A.edge i j) +
        ∑ i ∈ ofBoolRing x', ∑ j ∈ ofBoolRing y, A.edge i j
    exact folkmanNativeCode_sum_symmDiff
      (fun i => ∑ j ∈ ofBoolRing y, A.edge i j) _ _
  add_right := by
    intro x y y'
    change (∑ i ∈ ofBoolRing x,
        ∑ j ∈ symmDiff (ofBoolRing y) (ofBoolRing y'), A.edge i j) =
      (∑ i ∈ ofBoolRing x, ∑ j ∈ ofBoolRing y, A.edge i j) +
        ∑ i ∈ ofBoolRing x, ∑ j ∈ ofBoolRing y', A.edge i j
    simp_rw [folkmanNativeCode_sum_symmDiff]
    rw [Finset.sum_add_distrib]

/-- Realisation retains every specified atom-to-atom pairing value. -/
theorem folkmanNativeCodeRealisation_singletons (A : FolkmanAtomStructure)
    (i : Fin A.leftCount) (j : Fin A.rightCount) :
    (folkmanNativeCodeRealisation A).pairing
      (toBoolRing {i}) (toBoolRing {j}) = A.edge i j := by
  simp [folkmanNativeCodeRealisation]

/-- Isomorphism in the two-sorted native ring language, including the
original cross-pairing on all elements of both sorts. -/
structure FolkmanNativeFinitePairingIso
    {L R L' R' : Type*}
    [BooleanRing L] [BooleanRing R]
    [BooleanRing L'] [BooleanRing R']
    (P : FolkmanNativeFinitePairing L R)
    (Q : FolkmanNativeFinitePairing L' R') where
  left : L ≃+* L'
  right : R ≃+* R'
  preserves_pairing : ∀ x y, Q.pairing (left x) (right y) = P.pairing x y

end SuccessorTree.NonPrecompact
