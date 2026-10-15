import BANANA.NonPrecompact.PrebananaFiveAryDescendantParity

/-!
# Concatenating five-ary words and their descendant markings

A stage-n word w followed by a length-k suffix s represents an
atom of the stage-(n+k) Boolean algebra. Its marking equals the
descendant mark of s below a parent marked by the original mark of w.

This gives the exact bridge between the finite tower and the local
suffix-witness lemmas. Concatenating words also preserves both
components injectively: distinct roots or distinct suffixes cannot
produce the same ambient atom.

Selection of compatible target witnesses, the induced finite
Boolean embedding and countable limit remain separate obligations.
-/

namespace SuccessorTree.NonPrecompact

/-- The mark of a concatenated ambient word is the descendant mark
of its suffix below the mark of the prefix. -/
theorem prebananaFiveAryWordMark_append
    (n k : ℕ) (w : PrebananaFiveAryWord n)
    (s : PrebananaFiveAryWord k) :
    prebananaFiveAryWordMark (n + k) (Fin.append w s) =
      prebananaFiveAryDescendantMark
        (prebananaFiveAryWordMark n w) k s := by
  induction k with
  | zero =>
      have hs : s = (Fin.elim0 : Fin 0 → Fin 5) := Subsingleton.elim _ _
      subst s
      simp [prebananaFiveAryDescendantMark]
  | succ k ih =>
      cases s using Fin.snocCases with
      | snoc s c =>
          rw [Fin.append_snoc, Nat.add_succ,
            prebananaFiveAryWordMark_snoc,
            prebananaFiveAryDescendantMark_snoc, ih]

/-- Concatenation uniquely determines both the prefix and suffix. -/
theorem prebananaFiveAryWord_append_injective
    (n k : ℕ)
    (w v : PrebananaFiveAryWord n)
    (s t : PrebananaFiveAryWord k)
    (h : Fin.append w s = Fin.append v t) :
    w = v ∧ s = t := by
  constructor
  · funext i
    have hi := congrFun h (Fin.castAdd k i)
    simpa only [Fin.append_left] using hi
  · funext i
    have hi := congrFun h (Fin.natAdd n i)
    simpa only [Fin.append_right] using hi

/-- For any fixed prefix, appending distinct suffixes
produces distinct ambient words. -/
theorem prebananaFiveAryWord_append_suffix_injective
    (n k : ℕ) (w : PrebananaFiveAryWord n) :
    Function.Injective (Fin.append w : PrebananaFiveAryWord k →
      PrebananaFiveAryWord (n + k)) := by
  intro s t h
  exact (prebananaFiveAryWord_append_injective n k w w s t h).2

end SuccessorTree.NonPrecompact
