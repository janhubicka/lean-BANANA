import BANANA.NonPrecompact.PrebananaFiniteClass
import BANANA.NonPrecompact.PrebananaAmalgamBridge
import BANANA.NonPrecompact.PrebananaGridTotal

/-!
# Finite tuple profiles for the pre-BANANA limit

The circulation proof of omega-categoricity observes that n Boolean
generators determine at most 2^n atom-membership patterns. Even
when many ambient atoms realise the same pattern, their F₂ marks
can be summed within that pattern.

The resulting finite record comprises the set of realised Boolean
patterns and a parity mark for each pattern. For fixed tuple length
there are only finitely many such records, independently of the
number of ambient atoms.

This is the finite *combinatorial signature* step. It does not on
its own formalise homogeneity of the Fraïssé limit or invoke the
Ryll–Nardzewski theorem.
-/

namespace SuccessorTree.NonPrecompact

open scoped BigOperators

/-- The membership truth-values of an atom in n distinguished
Boolean elements. -/
abbrev PrebananaTuplePattern (n : ℕ) : Type := Fin n → Bool

/-- Truth pattern of one atom in an n-tuple of Boolean elements. -/
def prebananaTupleAtomPattern
    {n : ℕ} {A : PrebananaAtomStructure}
    (tuple : Fin n → Finset (Fin A.atomCount))
    (a : Fin A.atomCount) : PrebananaTuplePattern n :=
  fun i => decide (a ∈ tuple i)

/-- Membership in each distinguished Boolean element is recovered
from its atom's corresponding truth-pattern coordinate. -/
theorem prebananaTupleAtomPattern_true_iff
    {n : ℕ} {A : PrebananaAtomStructure}
    (tuple : Fin n → Finset (Fin A.atomCount))
    (a : Fin A.atomCount) (i : Fin n) :
    prebananaTupleAtomPattern tuple a i = true ↔ a ∈ tuple i := by
  simp [prebananaTupleAtomPattern]

/-- A finite tuple record: which of the 2^n Boolean membership
patterns occur, and the F₂ sum of marks at each pattern. -/
abbrev PrebananaTupleProfileRecord (n : ℕ) : Type :=
  Finset (PrebananaTuplePattern n) × (PrebananaTuplePattern n → F2)

/-- For every tuple length, only finitely many such records exist. -/
theorem prebananaTupleProfileRecord_finite (n : ℕ) :
    Finite (PrebananaTupleProfileRecord n) := by
  classical
  infer_instance

/-- The parity marking of one pattern is the sum of all ambient
atom marks realising that pattern. -/
noncomputable def prebananaTuplePatternMark
    {n : ℕ} (A : PrebananaAtomStructure)
    (tuple : Fin n → Finset (Fin A.atomCount))
    (pattern : PrebananaTuplePattern n) : F2 :=
  ∑ a : {a : Fin A.atomCount //
      prebananaTupleAtomPattern tuple a = pattern}, A.mark a.1

/-- The canonical finite record associated with any tuple in a
finite pre-BANANA atom presentation. -/
noncomputable def prebananaTupleProfileRecord
    {n : ℕ} (A : PrebananaAtomStructure)
    (tuple : Fin n → Finset (Fin A.atomCount)) :
    PrebananaTupleProfileRecord n :=
  (Finset.univ.image (prebananaTupleAtomPattern tuple),
    prebananaTuplePatternMark A tuple)

/-- Grouping the ambient atom marks by their truth patterns
preserves the total parity, which is zero for a pre-BANANA object. -/
theorem prebananaTuplePatternMark_total_zero
    {n : ℕ} (A : PrebananaAtomStructure)
    (tuple : Fin n → Finset (Fin A.atomCount)) :
    (∑ pattern : PrebananaTuplePattern n,
      prebananaTuplePatternMark A tuple pattern) = 0 := by
  classical
  calc
    (∑ pattern : PrebananaTuplePattern n,
        prebananaTuplePatternMark A tuple pattern) =
      ∑ a : Fin A.atomCount, A.mark a := by
        simpa [prebananaTuplePatternMark] using
          (Fintype.sum_fiberwise (prebananaTupleAtomPattern tuple) A.mark)
    _ = 0 := by
      have h := A.total_mark_parity
      rw [prebananaMarkedCount_cast_eq_sum] at h
      simpa using h

end SuccessorTree.NonPrecompact
