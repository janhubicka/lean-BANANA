import BANANA.NonPrecompact.PrebananaFiniteBooleanTower
import Mathlib.Tactic.NormNum

/-!
# The five-ary atom-splitting parity rule

To construct an explicit pre-BANANA Fraïssé limit, every finite
atom is replaced by five children. Regardless of the parent's
mark p ∈ F₂, two children have mark zero, two have mark one,
and the last inherits p.

This module isolates the one-step parity rule. The infinite tower,
its finite extension property, and its ultrahomogeneous limit
are separate outstanding obligations.
-/

namespace SuccessorTree.NonPrecompact

/-- A five-child marking with two fixed zero marks, two fixed one
marks, and a fifth mark inherited from the parent. -/
def prebananaFiveAryChildMark (p : F2) (i : Fin 5) : F2 :=
  if i = 4 then p else if i = 2 ∨ i = 3 then 1 else 0

/-- There are always two explicitly unmarked children. -/
theorem prebananaFiveAryChildMark_zeros (p : F2) :
    prebananaFiveAryChildMark p 0 = 0 ∧
      prebananaFiveAryChildMark p 1 = 0 := by
  simp [prebananaFiveAryChildMark]

/-- There are always two explicitly marked children. -/
theorem prebananaFiveAryChildMark_ones (p : F2) :
    prebananaFiveAryChildMark p 2 = 1 ∧
      prebananaFiveAryChildMark p 3 = 1 := by
  simp [prebananaFiveAryChildMark]

/-- The last child inherits the parent's marking. -/
theorem prebananaFiveAryChildMark_last (p : F2) :
    prebananaFiveAryChildMark p 4 = p := by
  rfl

/-- The sum of all five children's marks equals the parent's
mark. This is the finite compatibility needed by the tower
embeddings on the Boolean algebra of sets of words. -/
theorem prebananaFiveAryChildMark_total (p : F2) :
    (∑ i : Fin 5, prebananaFiveAryChildMark p i) = p := by
  have htwo : (1 : F2) + 1 = 0 := by decide
  norm_num [Fin.sum_univ_succ, prebananaFiveAryChildMark]
  simpa only [← add_assoc, htwo, zero_add]

end SuccessorTree.NonPrecompact
