import BANANA.NonPrecompact.FolkmanNativeRingAtomEquiv
import BANANA.NonPrecompact.FolkmanGeneratedNonunitalRingIso

/-!
# Native finite Boolean-ring terms in canonical atom coordinates

This module is the source-level handover between Track C's
non-unital term-equation classification and the canonical native
finite Boolean-ring atom representation already on main.

The representation preserves zero, addition and multiplication.
We reuse the generic term-evaluation naturality theorem rather
than duplicating an induction over ring terms.

No unit-preservation assumption is used for embeddings, and the
one-element zero ring is allowed. No statement about a homogeneous
countable limit is made here.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical symmDiff

-- The finite instance is needed while elaborating the target atom
-- carrier in the theorem statements, not merely inside their proofs.
local instance folkmanAsBoolAlgFiniteForRingTerms
    (α : Type*) [Fintype α] : Fintype (AsBoolAlg α) :=
  Fintype.ofEquiv α toBoolAlg

/-- Ring-term evaluation commutes with the native finite atom code.
The target uses the non-unital ring operations inherited by AsBoolRing. -/
theorem FolkmanRingTerm.eval_nativeAtomCoordinates
    (α : Type*) [BooleanRing α] [Fintype α]
    {n : ℕ} (xs : Fin n → α) (t : FolkmanRingTerm n) :
    toBoolRing (folkmanNativeRingAtomEquiv α (t.eval xs)) =
      t.eval (fun i => toBoolRing (folkmanNativeRingAtomEquiv α (xs i))) := by
  classical
  let f : α →
      AsBoolRing (Finset (PrebananaAbstractAtoms (AsBoolAlg α))) :=
    fun x => toBoolRing (folkmanNativeRingAtomEquiv α x)
  have hzero : f 0 = 0 := by
    change toBoolRing (folkmanNativeRingAtomEquiv α (0 : α)) = 0
    rw [folkmanNativeRingAtomEquiv_zero]
    rfl
  have hadd : ∀ x y : α, f (x + y) = f x + f y := by
    intro x y
    change toBoolRing (folkmanNativeRingAtomEquiv α (x + y)) =
      toBoolRing (folkmanNativeRingAtomEquiv α x) +
        toBoolRing (folkmanNativeRingAtomEquiv α y)
    rw [folkmanNativeRingAtomEquiv_add, toBoolRing_symmDiff]
  have hmul : ∀ x y : α, f (x * y) = f x * f y := by
    intro x y
    change toBoolRing (folkmanNativeRingAtomEquiv α (x * y)) =
      toBoolRing (folkmanNativeRingAtomEquiv α x) *
        toBoolRing (folkmanNativeRingAtomEquiv α y)
    rw [folkmanNativeRingAtomEquiv_mul, toBoolRing_inf]
  exact FolkmanRingTerm.eval_map f hzero hadd hmul xs t

/-- The original native carrier and its atom code satisfy exactly
the same equations between non-unital ring terms. -/
theorem folkmanRingTerm_nativeAtomCoordinates_eq_iff
    (α : Type*) [BooleanRing α] [Fintype α]
    {n : ℕ} (xs : Fin n → α)
    (t u : FolkmanRingTerm n) :
    t.eval xs = u.eval xs ↔
      t.eval (fun i => toBoolRing (folkmanNativeRingAtomEquiv α (xs i))) =
        u.eval (fun i => toBoolRing (folkmanNativeRingAtomEquiv α (xs i))) := by
  classical
  constructor
  · intro h
    calc
      t.eval (fun i => toBoolRing (folkmanNativeRingAtomEquiv α (xs i))) =
          toBoolRing (folkmanNativeRingAtomEquiv α (t.eval xs)) :=
        (t.eval_nativeAtomCoordinates α xs).symm
      _ = toBoolRing (folkmanNativeRingAtomEquiv α (u.eval xs)) :=
        congrArg (fun z : α => toBoolRing (folkmanNativeRingAtomEquiv α z)) h
      _ = u.eval (fun i => toBoolRing (folkmanNativeRingAtomEquiv α (xs i))) :=
        u.eval_nativeAtomCoordinates α xs
  · intro h
    apply (folkmanNativeRingAtomEquiv α).injective
    apply toBoolRing.injective
    calc
      toBoolRing (folkmanNativeRingAtomEquiv α (t.eval xs)) =
          t.eval (fun i => toBoolRing (folkmanNativeRingAtomEquiv α (xs i))) :=
        t.eval_nativeAtomCoordinates α xs
      _ = u.eval (fun i => toBoolRing (folkmanNativeRingAtomEquiv α (xs i))) := h
      _ = toBoolRing (folkmanNativeRingAtomEquiv α (u.eval xs)) :=
        (u.eval_nativeAtomCoordinates α xs).symm

/-- Equations transferred through two atom codes give a native
generated non-unital ring equivalence; the remaining class-specific
input is equality of the finite coordinate profiles. -/
noncomputable def folkmanNativeGeneratedRingEquiv_of_coordinateEqualities
    (α β : Type*)
    [BooleanRing α] [Fintype α]
    [BooleanRing β] [Fintype β]
    {n : ℕ} (xs : Fin n → α) (ys : Fin n → β)
    (h : ∀ t u : FolkmanRingTerm n,
      (t.eval (fun i => toBoolRing (folkmanNativeRingAtomEquiv α (xs i))) =
        u.eval (fun i => toBoolRing (folkmanNativeRingAtomEquiv α (xs i)))) ↔
      (t.eval (fun i => toBoolRing (folkmanNativeRingAtomEquiv β (ys i))) =
        u.eval (fun i => toBoolRing (folkmanNativeRingAtomEquiv β (ys i))))) :
    folkmanGeneratedNonunitalSubring xs ≃+*
      folkmanGeneratedNonunitalSubring ys :=
  folkmanGeneratedNonunitalRingEquiv_of_termEqualities xs ys (by
    intro t u
    exact (folkmanRingTerm_nativeAtomCoordinates_eq_iff α xs t u).trans
      ((h t u).trans
        (folkmanRingTerm_nativeAtomCoordinates_eq_iff β ys t u).symm))

end SuccessorTree.NonPrecompact
