import BANANA.NonPrecompact.PrebananaSingleSpecialSuffix

/-!
# Distinct mark-compatible suffixes indexed by target atoms

Given any finite list of desired F₂ marks indexed by Fin k,
assign position i the length-k suffix that is 4 everywhere except
at i, where it is 0 for an unmarked target or 2 for a marked target.

The construction gives one distinct suffix for every target atom,
and its final mark equals the desired target mark regardless of the
original parent atom's mark. This is the injective selection lemma
needed by the pre-BANANA finite-extension construction.

Embedding the list in an arbitrary target-atom indexing and
assembling a marked partition remain separate obligations.
-/

namespace SuccessorTree.NonPrecompact

/-- Letter that resets the current mark to the prescribed F₂ value. -/
def prebananaSuffixLetter (m : F2) : Fin 5 :=
  if m = 0 then 0 else 2

/-- Neither prescribed-mark letter is the inherited-mark letter 4. -/
theorem prebananaSuffixLetter_ne_four (m : F2) :
    prebananaSuffixLetter m ≠ (4 : Fin 5) := by
  by_cases hm : m = 0 <;> simp [prebananaSuffixLetter, hm]

/-- The chosen letter resets a parent of *any* parity to m. -/
theorem prebananaSuffixLetter_mark (p m : F2) :
    prebananaFiveAryChildMark p (prebananaSuffixLetter m) = m := by
  fin_cases m <;>
    simp [prebananaSuffixLetter, prebananaFiveAryChildMark]

/-- The concrete suffix selected for each target atom position. -/
def prebananaSelectedSuffix (k : ℕ) (mark : Fin k → F2)
    (i : Fin k) : PrebananaFiveAryWord k :=
  prebananaSingleSpecialSuffix k i (prebananaSuffixLetter (mark i))

/-- Every selected suffix has exactly the desired mark below any parent. -/
theorem prebananaSelectedSuffix_mark
    (p : F2) (k : ℕ) (mark : Fin k → F2) (i : Fin k) :
    prebananaFiveAryDescendantMark p k
      (prebananaSelectedSuffix k mark i) = mark i := by
  exact (prebananaSingleSpecialSuffix_mark p
    (prebananaSuffixLetter (mark i)) k i).trans
      (prebananaSuffixLetter_mark p (mark i))

/-- The selected suffixes are injectively indexed by target atoms,
even when their prescribed marks differ. -/
theorem prebananaSelectedSuffix_injective
    (k : ℕ) (mark : Fin k → F2) :
    Function.Injective (prebananaSelectedSuffix k mark) := by
  intro i j hij
  by_contra hne
  have heq := congrFun hij i
  have hbad : prebananaSuffixLetter (mark i) = (4 : Fin 5) := by
    simpa only [prebananaSelectedSuffix, prebananaSingleSpecialSuffix,
      if_pos rfl, if_neg hne] using heq
  exact prebananaSuffixLetter_ne_four (mark i) hbad

end SuccessorTree.NonPrecompact
