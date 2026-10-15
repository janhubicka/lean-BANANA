import BANANA.NonPrecompact.PrebananaFiveAryWordLift
import Mathlib

/-!
# Marking preservation for the five-ary word lift

The Boolean inverse-image map under the prefix projection preserves
the F₂ marking because the marks on the five extensions of each word
sum to the mark on that word.

This is the key finite-fibre sum identity for constructing an actual
tower of finite marked Boolean algebras. The countable direct limit,
finite extension property and ultrahomogeneity are not claimed here.
-/

namespace SuccessorTree.NonPrecompact

/-- The one-step inverse-image map on word subsets preserves their
disjoint-additive F₂ marking. -/
theorem prebananaFiveAryWordLift_preserves_mark
    (n : ℕ) (s : Finset (PrebananaFiveAryWord n)) :
    (∑ w ∈ prebananaFiveAryWordLift n s,
      prebananaFiveAryWordMark (n + 1) w) =
    (∑ w ∈ s, prebananaFiveAryWordMark n w) := by
  classical
  have hsum :
      (∑ p : Fin 5 × PrebananaFiveAryWord n,
        if p.2 ∈ s then
          prebananaFiveAryWordMark (n + 1) (Fin.snoc p.2 p.1)
        else 0) =
      (∑ w : PrebananaFiveAryWord n,
        if w ∈ s then prebananaFiveAryWordMark n w else 0) := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro w hw
    by_cases hmem : w ∈ s
    · simpa only [hmem, ite_true] using
        (prebananaFiveAryWordMark_sum_children n w)
    · simp [hmem]
  calc
    (∑ w ∈ prebananaFiveAryWordLift n s,
      prebananaFiveAryWordMark (n + 1) w) =
        ∑ w : PrebananaFiveAryWord (n + 1),
          if prebananaFiveAryPrefix n w ∈ s then
            prebananaFiveAryWordMark (n + 1) w else 0 := by
              simp [prebananaFiveAryWordLift, Finset.sum_filter]
    _ =
        ∑ p : Fin 5 × PrebananaFiveAryWord n,
          if p.2 ∈ s then
            prebananaFiveAryWordMark (n + 1) (Fin.snoc p.2 p.1)
          else 0 := by
            let e : (Fin 5 × PrebananaFiveAryWord n) ≃
                PrebananaFiveAryWord (n + 1) :=
              Fin.snocEquiv (fun _ : Fin (n + 1) => Fin 5)
            exact (Fintype.sum_equiv e
              (fun p => if p.2 ∈ s then
                prebananaFiveAryWordMark (n + 1) (Fin.snoc p.2 p.1)
                else 0)
              (fun w => if prebananaFiveAryPrefix n w ∈ s then
                prebananaFiveAryWordMark (n + 1) w else 0)
              (fun p => by
                have he : e p = Fin.snoc p.2 p.1 := rfl
                rw [he, prebananaFiveAryPrefix_snoc])).symm
    _ = ∑ w : PrebananaFiveAryWord n,
        if w ∈ s then prebananaFiveAryWordMark n w else 0 := hsum
    _ = (∑ w ∈ s, prebananaFiveAryWordMark n w) := by
          simp [Finset.sum_filter]

end SuccessorTree.NonPrecompact
