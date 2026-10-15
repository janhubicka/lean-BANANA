import BANANA.NonPrecompact.PrebananaFiveAryWordStage

/-!
# Prefix maps between the finite word stages

The connecting map from length-(n+1) atoms to length-n atoms
forgets the last letter. Each prefix has five extensions.

Together with the already verified child-mark sum, this is the
word-level ingredient needed to construct a marked Boolean
embedding between successive finite stages. The reindexing to
the Fin atom coordinates is still to be formalised.
-/

namespace SuccessorTree.NonPrecompact

/-- Delete the last letter of a five-ary word. -/
def prebananaFiveAryPrefix (n : ℕ) :
    PrebananaFiveAryWord (n + 1) → PrebananaFiveAryWord n :=
  Fin.init

/-- Appending any child letter and then dropping it recovers the parent. -/
theorem prebananaFiveAryPrefix_snoc (n : ℕ)
    (w : PrebananaFiveAryWord n) (c : Fin 5) :
    prebananaFiveAryPrefix n (Fin.snoc w c) = w := by
  simpa [prebananaFiveAryPrefix] using (Fin.init_snoc c w)

/-- Every finite word admits a one-step extension. -/
theorem prebananaFiveAryPrefix_surjective (n : ℕ) :
    Function.Surjective (prebananaFiveAryPrefix n) := by
  intro w
  exact ⟨Fin.snoc w 0, prebananaFiveAryPrefix_snoc n w 0⟩

/-- Any extended word is determined by its prefix and its final letter. -/
theorem prebananaFiveAryPrefix_snoc_last (n : ℕ)
    (w : PrebananaFiveAryWord (n + 1)) :
    Fin.snoc (prebananaFiveAryPrefix n w) (w (Fin.last n)) = w := by
  exact Fin.snoc_init_self w

/-- The five extensions of a prefix carry exactly the total
mark prescribed for the prefix. -/
theorem prebananaFiveAryPrefix_mark_sum (n : ℕ)
    (w : PrebananaFiveAryWord n) :
    (∑ c : Fin 5,
        prebananaFiveAryWordMark (n + 1) (Fin.snoc w c)) =
      prebananaFiveAryWordMark n w :=
  prebananaFiveAryWordMark_sum_children n w

end SuccessorTree.NonPrecompact
