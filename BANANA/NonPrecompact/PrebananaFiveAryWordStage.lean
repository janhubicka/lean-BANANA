import BANANA.NonPrecompact.PrebananaFiveAryWordMark
import BANANA.NonPrecompact.PrebananaIndexedParity

/-!
# The actual finite stages of the five-ary pre-BANANA tower

A stage is the Boolean powerset of all five-ary words of a
fixed length, marked according to the recursive word marking.
The sum of the marks of all words at each level is zero.

This verifies each finite stage as an admissible marked Boolean
algebra in the atom-coordinate presentation. Marking-preserving
connecting embeddings are constructed in the subsequent word-lift
modules. The direct limit and extension property remain open.
-/

namespace SuccessorTree.NonPrecompact

/-- At every length the total parity of all word atoms is zero. -/
theorem prebananaFiveAryWordMark_total (n : ℕ) :
    (∑ w : PrebananaFiveAryWord n, prebananaFiveAryWordMark n w) = 0 := by
  induction n with
  | zero =>
      simp [prebananaFiveAryWordMark]
  | succ n ih =>
      classical
      let e : (Fin 5 × PrebananaFiveAryWord n) ≃
          PrebananaFiveAryWord (n + 1) :=
        Fin.snocEquiv (fun _ : Fin (n + 1) => Fin 5)
      have hs :
          (∑ w : PrebananaFiveAryWord (n + 1),
            prebananaFiveAryWordMark (n + 1) w) =
          ∑ p : Fin 5 × PrebananaFiveAryWord n,
            prebananaFiveAryWordMark (n + 1) (Fin.snoc p.2 p.1) := by
        exact (Fintype.sum_equiv e
          (fun p => prebananaFiveAryWordMark (n + 1)
            (Fin.snoc p.2 p.1))
          (prebananaFiveAryWordMark (n + 1))
          (fun p => rfl)).symm
      calc
        (∑ w : PrebananaFiveAryWord (n + 1),
          prebananaFiveAryWordMark (n + 1) w) =
            ∑ p : Fin 5 × PrebananaFiveAryWord n,
              prebananaFiveAryWordMark (n + 1)
                (Fin.snoc p.2 p.1) := hs
        _ = ∑ c : Fin 5, ∑ w : PrebananaFiveAryWord n,
              prebananaFiveAryWordMark (n + 1) (Fin.snoc w c) := by
              rw [Fintype.sum_prod_type]
        _ = ∑ w : PrebananaFiveAryWord n, ∑ c : Fin 5,
              prebananaFiveAryWordMark (n + 1) (Fin.snoc w c) := by
              rw [Finset.sum_comm]
        _ = ∑ w : PrebananaFiveAryWord n,
              prebananaFiveAryWordMark n w := by
              simp only [prebananaFiveAryWordMark_sum_children]
        _ = 0 := ih

/-- The standard indexed finite pre-BANANA atom presentation
of all length-n five-ary words. -/
noncomputable def prebananaFiveAryAtomStage (n : ℕ) :
    PrebananaAtomStructure where
  atomCount := Fintype.card (PrebananaFiveAryWord n)
  atomCount_pos := by
    classical
    exact Fintype.card_pos_iff.mpr ⟨fun _ => (0 : Fin 5)⟩
  mark := fun i =>
    prebananaFiveAryWordMark n
      ((Fintype.equivFin (PrebananaFiveAryWord n)).symm i)
  total_mark_parity := by
    classical
    exact (prebananaMarkedCount_reindex_eq_sum
      (Fintype.equivFin (PrebananaFiveAryWord n)).symm
      (prebananaFiveAryWordMark n)).trans
      (prebananaFiveAryWordMark_total n)

end SuccessorTree.NonPrecompact
