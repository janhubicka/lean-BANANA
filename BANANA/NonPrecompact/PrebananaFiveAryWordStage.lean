import BANANA.NonPrecompact.PrebananaFiveAryWordMark
import BANANA.NonPrecompact.PrebananaIndexedParity
import BANANA.NonPrecompact.PrebananaFiveAryWordBasics

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
