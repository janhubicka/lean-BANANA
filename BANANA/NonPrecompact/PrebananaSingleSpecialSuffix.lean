import BANANA.NonPrecompact.PrebananaFiveAryDescendantParity

/-!
# Explicit distinguishable descendants of both marks

At depth k below any parent, place one exceptional letter c at one
position j and put the inherited-mark letter 4 everywhere else.
If c=0 the descendant is unmarked; if c=2 it is marked.
Different positions give different words, and the two families
of witness words are disjoint.

Consequently, at least k descendants of each mark are visibly
available without deriving an exact descendant-count formula.
This constructs the witness maps and proves their injectivity and
marking; allocating other atoms and the finite extension remain
separate steps.
-/

namespace SuccessorTree.NonPrecompact

/-- The length-k word equal to c at position j and 4 elsewhere. -/
def prebananaSingleSpecialSuffix (k : ℕ) (j : Fin k) (c : Fin 5) :
    PrebananaFiveAryWord k :=
  fun i => if i = j then c else 4

/-- Changing the distinguished position changes the word,
provided the distinguished letter is not 4. -/
theorem prebananaSingleSpecialSuffix_injective
    (k : ℕ) (c : Fin 5) (hc : c ≠ 4) :
    Function.Injective (fun j : Fin k => prebananaSingleSpecialSuffix k j c) := by
  intro i j h
  by_contra hij
  have heq := congrFun h i
  have hbad : c = (4 : Fin 5) := by
    simpa [prebananaSingleSpecialSuffix, hij] using heq
  exact hc hbad

/-- Appending the inherited-mark letter 4 repeatedly leaves
the parent's mark unchanged. -/
theorem prebananaFiveAryDescendantMark_all4 (p : F2) (k : ℕ) :
    prebananaFiveAryDescendantMark p k (fun _ => 4) = p := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change prebananaFiveAryChildMark
        (prebananaFiveAryDescendantMark p k (fun _ => 4)) 4 = p
      rw [prebananaFiveAryChildMark_last, ih]

/-- A single exceptional letter has exactly the mark dictated by
the five-ary child rule, independently of its position. -/
theorem prebananaSingleSpecialSuffix_mark
    (p : F2) (c : Fin 5) (k : ℕ) (j : Fin k) :
    prebananaFiveAryDescendantMark p k
        (prebananaSingleSpecialSuffix k j c) =
      prebananaFiveAryChildMark p c := by
  induction k with
  | zero => exact Fin.elim0 j
  | succ k ih =>
      rcases j.eq_castSucc_or_eq_last with ⟨j, rfl⟩ | rfl
      · have hword :
            prebananaSingleSpecialSuffix (k + 1) j.castSucc c =
            Fin.snoc (prebananaSingleSpecialSuffix k j c) 4 := by
          funext t
          rcases t.eq_castSucc_or_eq_last with ⟨t, rfl⟩ | rfl
          · simp [prebananaSingleSpecialSuffix]
          · have hne : (Fin.last k : Fin (k + 1)) ≠ j.castSucc :=
              (Fin.castSucc_ne_last j).symm
            simp [prebananaSingleSpecialSuffix, hne]
        rw [hword, prebananaFiveAryDescendantMark_snoc,
          prebananaFiveAryChildMark_last]
        exact ih j
      · have hword :
            prebananaSingleSpecialSuffix (k + 1) (Fin.last k) c =
            Fin.snoc (fun _ : Fin k => (4 : Fin 5)) c := by
          funext t
          rcases t.eq_castSucc_or_eq_last with ⟨t, rfl⟩ | rfl
          · have hne : (Fin.last k : Fin (k + 1)) ≠ t.castSucc :=
              (Fin.castSucc_ne_last t).symm
            simp [prebananaSingleSpecialSuffix, hne]
          · simp [prebananaSingleSpecialSuffix]
        rw [hword, prebananaFiveAryDescendantMark_snoc,
          prebananaFiveAryDescendantMark_all4]

/-- The chosen letters 0 and 2 give unmarked and marked
descendants respectively, for every parent mark. -/
theorem prebananaSingleSpecialSuffix_both_marks
    (p : F2) (k : ℕ) (j : Fin k) :
    prebananaFiveAryDescendantMark p k
      (prebananaSingleSpecialSuffix k j 0) = 0 ∧
    prebananaFiveAryDescendantMark p k
      (prebananaSingleSpecialSuffix k j 2) = 1 := by
  constructor
  · simpa [prebananaFiveAryChildMark] using
      (prebananaSingleSpecialSuffix_mark p 0 k j)
  · simpa [prebananaFiveAryChildMark] using
      (prebananaSingleSpecialSuffix_mark p 2 k j)

end SuccessorTree.NonPrecompact
