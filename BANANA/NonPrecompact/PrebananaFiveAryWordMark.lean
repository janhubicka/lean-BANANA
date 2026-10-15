import BANANA.NonPrecompact.PrebananaFiveAryDescendantCounts

/-!
# Marks on actual finite words of the five-ary pre-BANANA tower

An atom at level n is an n-letter word over Fin 5. Its mark is
defined by starting with zero at the empty word, and applying the
five-child rule to the final letter at every extension.

This module verifies the *actual word-level* one-step rule, rather
than merely the numerical recurrence for descendant counts. The
finite-set Boolean algebras, the maps between them, and the
Fraïssé-limit extension property are separate obligations.
-/

namespace SuccessorTree.NonPrecompact

/-- A word of length n over a five-letter alphabet. -/
abbrev PrebananaFiveAryWord (n : ℕ) := Fin n → Fin 5

/-- Recursively mark the finite words of a five-ary tree.
The empty word has mark zero. -/
def prebananaFiveAryWordMark :
    (n : ℕ) → PrebananaFiveAryWord n → F2
  | 0, _ => 0
  | n + 1, w =>
      prebananaFiveAryChildMark
        (prebananaFiveAryWordMark n (fun i => w i.castSucc))
        (w (Fin.last n))

/-- Extending a word by one letter applies exactly the
five-ary child-mark rule to its previous mark. -/
theorem prebananaFiveAryWordMark_snoc
    (n : ℕ) (w : PrebananaFiveAryWord n) (c : Fin 5) :
    prebananaFiveAryWordMark (n + 1) (Fin.snoc w c) =
      prebananaFiveAryChildMark (prebananaFiveAryWordMark n w) c := by
  simp [prebananaFiveAryWordMark]

/-- The marks of all five immediate children sum to the
mark of their common parent. -/
theorem prebananaFiveAryWordMark_sum_children
    (n : ℕ) (w : PrebananaFiveAryWord n) :
    (∑ c : Fin 5, prebananaFiveAryWordMark (n + 1)
        (Fin.snoc w c)) = prebananaFiveAryWordMark n w := by
  simp only [prebananaFiveAryWordMark_snoc]
  exact prebananaFiveAryChildMark_total _

/-- The empty word has mark zero. -/
theorem prebananaFiveAryWordMark_empty
    (w : PrebananaFiveAryWord 0) :
    prebananaFiveAryWordMark 0 w = 0 := rfl

end SuccessorTree.NonPrecompact
