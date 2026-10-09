import BANANA.NonPrecompact.BananaLimitGlobalHomogeneity
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Finite tuple signatures for the explicit BANANA pairing

For fixed lengths l and r of ordered tuples on the two sorts, record
(1) every linear dependency between the l left entries,
(2) every linear dependency between the r right entries, and
(3) the l-by-r table of pairings.

There are finitely many such signatures. This is the first step of
the Rosenstein/Ryll–Nardzewski finite-orbit argument from the
circulation manuscript. Establishing that equal signatures imply
conjugacy by a global automorphism is a separate obligation.
-/

namespace SuccessorTree.NonPrecompact

/-- The linear combination of the entries of a finite tuple. -/
noncomputable def bananaLimitTupleCombination {n : ℕ}
    (a : Fin n → BananaLimitVector) :
    (Fin n → F2) →ₗ[F2] BananaLimitVector :=
  Fintype.linearCombination F2 a

/-- The potential orbit invariant for an ordered left/right tuple pair.
The Boolean-valued functions record all linear relations, while the
last component records cross-pairings. -/
abbrev BananaLimitTupleSignature (l r : ℕ) : Type :=
  ((Fin l → F2) → Bool) ×
  (((Fin r → F2) → Bool) × (Fin l → Fin r → F2))

/-- Every fixed arity has finitely many possible tuple signatures. -/
theorem bananaLimitTupleSignature_finite (l r : ℕ) :
    Finite (BananaLimitTupleSignature l r) := by
  infer_instance

/-- The complete signature of an ordered pair of finite tuples. -/
noncomputable def bananaLimitTupleSignature {l r : ℕ}
    (a : Fin l → BananaLimitVector)
    (b : Fin r → BananaLimitVector) :
    BananaLimitTupleSignature l r :=
  (fun c => decide (bananaLimitTupleCombination a c = 0),
   fun d => decide (bananaLimitTupleCombination b d = 0),
   fun i j => bananaLimitPairing (a i) (b j))

/-- The left relation bit is true precisely for a vanishing
linear combination. -/
theorem bananaLimitTupleSignature_left_relation {l r : ℕ}
    (a : Fin l → BananaLimitVector)
    (b : Fin r → BananaLimitVector) (c : Fin l → F2) :
    (bananaLimitTupleSignature a b).1 c = true ↔
      bananaLimitTupleCombination a c = 0 := by
  classical
  simp [bananaLimitTupleSignature]

/-- The right relation bit has the analogous exact interpretation. -/
theorem bananaLimitTupleSignature_right_relation {l r : ℕ}
    (a : Fin l → BananaLimitVector)
    (b : Fin r → BananaLimitVector) (d : Fin r → F2) :
    (bananaLimitTupleSignature a b).2.1 d = true ↔
      bananaLimitTupleCombination b d = 0 := by
  classical
  simp [bananaLimitTupleSignature]

/-- The last component records the actual pairing on tuple entries. -/
theorem bananaLimitTupleSignature_pairing {l r : ℕ}
    (a : Fin l → BananaLimitVector)
    (b : Fin r → BananaLimitVector)
    (i : Fin l) (j : Fin r) :
    (bananaLimitTupleSignature a b).2.2 i j =
      bananaLimitPairing (a i) (b j) := rfl

/-- A single coefficient equal to one picks out the associated entry. -/
theorem bananaLimitTupleCombination_single {n : ℕ}
    (a : Fin n → BananaLimitVector) (i : Fin n) :
    bananaLimitTupleCombination a (Pi.single i 1) = a i := by
  classical
  simpa [bananaLimitTupleCombination] using
    (Fintype.linearCombination_apply_single F2 a i (1 : F2))

end SuccessorTree.NonPrecompact
