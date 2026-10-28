import BANANA.NonPrecompact.FolkmanFiniteClassData

/-!
# An additive Folkman pairing is determined by its atom matrix

A finite Boolean ring is a powerset of its atoms, with symmetric
difference as addition.  Every pairing additive in both arguments
therefore equals the finite double sum of its singleton-atom values.

This elementary representation lemma is independent of the particular
atom-grid strong-amalgamation construction.  It is the missing matrix
reconstruction step in transporting arbitrary finite native Folkman
objects to the countable family of finite atom presentations.

No nonempty-atom assumption is used, so both zero-ring sorts are
included.  The lemma is stated for arbitrary atom types, not only Fin.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical symmDiff BigOperators

/-- Additivity for symmetric difference forces the empty left support
to have pairing value zero. -/
theorem folkmanAtomPairing_empty_left
    {I J : Type*}
    (β : Finset I → Finset J → F2)
    (hleft : ∀ s t u, β (symmDiff s t) u = β s u + β t u)
    (u : Finset J) :
    β ∅ u = 0 := by
  have h : β ∅ u = β ∅ u + β ∅ u := by
    simpa using hleft (∅ : Finset I) ∅ u
  have h' : β ∅ u + 0 = β ∅ u + β ∅ u := by
    simpa using h
  exact (add_left_cancel h').symm

/-- Additivity for symmetric difference forces the empty right support
to have pairing value zero. -/
theorem folkmanAtomPairing_empty_right
    {I J : Type*}
    (β : Finset I → Finset J → F2)
    (hright : ∀ s t u, β s (symmDiff t u) = β s t + β s u)
    (s : Finset I) :
    β s ∅ = 0 := by
  have h : β s ∅ = β s ∅ + β s ∅ := by
    simpa using hright s (∅ : Finset J) ∅
  have h' : β s ∅ + 0 = β s ∅ + β s ∅ := by
    simpa using h
  exact (add_left_cancel h').symm

/-- Every value of an additive pairing is a sum of its singleton
left-atom contributions. -/
theorem folkmanAtomPairing_sum_left
    {I J : Type*}
    (β : Finset I → Finset J → F2)
    (hleft : ∀ s t u, β (symmDiff s t) u = β s u + β t u)
    (s : Finset I) (u : Finset J) :
    β s u = ∑ i ∈ s, β {i} u := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using folkmanAtomPairing_empty_left β hleft u
  | @insert i s hi ih =>
      have hs : symmDiff ({i} : Finset I) s = insert i s := by
        ext j
        by_cases hji : j = i
        · subst j
          simp [Finset.mem_symmDiff, hi]
        · simp [Finset.mem_symmDiff, hji]
      calc
        β (insert i s) u = β (symmDiff ({i} : Finset I) s) u := by
          rw [hs]
        _ = β {i} u + β s u := hleft _ _ _
        _ = ∑ j ∈ insert i s, β {j} u := by
          simp [Finset.sum_insert hi, ih]

/-- Every value of an additive pairing is a sum of its singleton
right-atom contributions. -/
theorem folkmanAtomPairing_sum_right
    {I J : Type*}
    (β : Finset I → Finset J → F2)
    (hright : ∀ s t u, β s (symmDiff t u) = β s t + β s u)
    (s : Finset I) (t : Finset J) :
    β s t = ∑ j ∈ t, β s {j} := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      simpa using folkmanAtomPairing_empty_right β hright s
  | @insert j t hj ih =>
      have ht : symmDiff ({j} : Finset J) t = insert j t := by
        ext k
        by_cases hkj : k = j
        · subst k
          simp [Finset.mem_symmDiff, hj]
        · simp [Finset.mem_symmDiff, hkj]
      calc
        β s (insert j t) = β s (symmDiff ({j} : Finset J) t) := by
          rw [ht]
        _ = β s {j} + β s t := hright _ _ _
        _ = ∑ k ∈ insert j t, β s {k} := by
          simp [Finset.sum_insert hj, ih]

/-- Matrix reconstruction: an F₂-pairing additive under symmetric
difference in each argument is completely determined by its
singleton-atom values.  This also holds when either atom set is empty. -/
theorem folkmanAtomPairing_eq_doubleSum
    {I J : Type*}
    (β : Finset I → Finset J → F2)
    (hleft : ∀ s t u, β (symmDiff s t) u = β s u + β t u)
    (hright : ∀ s t u, β s (symmDiff t u) = β s t + β s u)
    (s : Finset I) (t : Finset J) :
    β s t = ∑ i ∈ s, ∑ j ∈ t, β {i} {j} := by
  rw [folkmanAtomPairing_sum_left β hleft s t]
  apply Finset.sum_congr rfl
  intro i hi
  exact folkmanAtomPairing_sum_right β hright {i} t

end SuccessorTree.NonPrecompact
