import BANANA.NonPrecompact.PrebananaFiveAryWordPrefix
import BANANA.NonPrecompact.PrebananaAbstractClassEPPA

/-!
# Actual finite Boolean stages of the five-ary construction

The finite Boolean algebra at depth n is the powerset of n-letter
words over Fin 5. The marking of a subset is the sum of the
recursive marks of its atoms.

Unlike the indexed atom presentation, the model here uses its actual
Boolean carrier. The statement that each finite stage is an
admissible pre-BANANA model follows from the all-level parity lemma.

Connecting maps and marking preservation are established in the
word-lift modules. The countable limit remains to be constructed.
-/

namespace SuccessorTree.NonPrecompact

/-- The actual finite marked Boolean algebra of all five-ary words
of a given length, with its inherited disjoint-additive marking. -/
noncomputable def prebananaFiveAryBooleanStage
    (n : ℕ) : PrebananaFiniteBooleanModel where
  carrier := Finset (PrebananaFiveAryWord n)
  booleanAlgebra := inferInstance
  finite := inferInstance
  nontrivial := by
    letI : Nonempty (PrebananaFiveAryWord n) := ⟨fun _ => 0⟩
    infer_instance
  μ := fun s => ∑ w ∈ s, prebananaFiveAryWordMark n w
  μ_bot := by
    simp
  μ_top := by
    simpa using prebananaFiveAryWordMark_total n
  μ_add := by
    intro x y hxy
    change
      (∑ w ∈ x ∪ y, prebananaFiveAryWordMark n w) =
      (∑ w ∈ x, prebananaFiveAryWordMark n w) +
      (∑ w ∈ y, prebananaFiveAryWordMark n w)
    exact Finset.sum_union
      (Finset.disjoint_iff_inter_eq_empty.mpr hxy)

end SuccessorTree.NonPrecompact
