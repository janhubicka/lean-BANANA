import BANANA.NonPrecompact.PrebananaBooleanTerms
import BANANA.NonPrecompact.PrebananaTupleSignatureEmbedding

/-!
# The marked parity of Boolean terms is determined by tuple profiles

Each Boolean term in a finite tuple selects a union of its atom
membership-pattern fibres. Regrouping the total F₂ mark by those
fibres shows that the mark of every Boolean-term evaluation is the
sum of its selected pattern marks.

Thus equal complete profiles determine the marked parity of every
Boolean term, complementing their classification of equations.
No infinite Fraïssé-limit orbit statement is asserted here.
-/

namespace SuccessorTree.NonPrecompact

open scoped BigOperators

/-- The parity of any Boolean-term evaluation is the sum of the
profile marks of those patterns on which that term is true. -/
theorem prebananaBooleanTerm_evalParity_eq_profile_sum
    {n : ℕ}
    (A : PrebananaAtomStructure)
    (tuple : Fin n → Finset (Fin A.atomCount))
    (t : PrebananaBooleanTerm n) :
    prebananaBooleanParity A (t.evalSet tuple) =
      ∑ p : Fin n → Bool,
        if t.evalPattern p = true then
          prebananaSignatureMark A tuple p else 0 := by
  classical
  let sig := prebananaAtomSignature A tuple
  have hPatternSum (p : Fin n → Bool) :
      (∑ a ∈ (t.evalSet tuple).filter (fun a => sig a = p), A.mark a) =
      if t.evalPattern p = true then
        prebananaSignatureMark A tuple p else 0 := by
    by_cases hp : t.evalPattern p = true
    · simp only [hp, if_true]
      have hset :
          (t.evalSet tuple).filter (fun a => sig a = p) =
            (Finset.univ : Finset (Fin A.atomCount)).filter
              (fun a => sig a = p) := by
        ext a
        constructor
        · intro ha
          exact (Finset.mem_filter.mp ha).2
        · intro ha
          have hs : sig a = p := (Finset.mem_filter.mp ha).2
          have heval : a ∈ t.evalSet tuple :=
            (t.mem_evalSet_iff_pattern A tuple a).mpr (by
              simpa [sig, hs] using hp)
          exact Finset.mem_filter.mpr ⟨heval, hs⟩
      rw [hset]
      rfl
    · simp only [hp, if_false]
      apply Finset.sum_eq_zero
      intro a ha
      have hmem : a ∈ t.evalSet tuple := (Finset.mem_filter.mp ha).1
      have hs : sig a = p := (Finset.mem_filter.mp ha).2
      have htrue := (t.mem_evalSet_iff_pattern A tuple a).mp hmem
      rw [show prebananaAtomSignature A tuple a = p from hs] at htrue
      exact (hp htrue).elim
  unfold prebananaBooleanParity
  rw [prebananaMarkedCount_cast_eq_sum]
  symm
  calc
    (∑ p : Fin n → Bool,
        if t.evalPattern p = true then
          prebananaSignatureMark A tuple p else 0) =
      ∑ p : Fin n → Bool,
        ∑ a ∈ (t.evalSet tuple).filter (fun a => sig a = p),
          A.mark a := by
        apply Finset.sum_congr rfl
        intro p hp
        exact (hPatternSum p).symm
    _ = ∑ a ∈ t.evalSet tuple, A.mark a :=
        Finset.sum_fiberwise (t.evalSet tuple) sig A.mark

/-- Equal complete profiles give the same F₂ marking for the
evaluation of every Boolean term in the distinguished tuple. -/
theorem prebananaBooleanTerm_parity_of_profile_eq
    {n : ℕ}
    (A B : PrebananaAtomStructure)
    (tupleA : Fin n → Finset (Fin A.atomCount))
    (tupleB : Fin n → Finset (Fin B.atomCount))
    (h : prebananaTupleProfile A tupleA =
      prebananaTupleProfile B tupleB)
    (t : PrebananaBooleanTerm n) :
    prebananaBooleanParity A (t.evalSet tupleA) =
      prebananaBooleanParity B (t.evalSet tupleB) := by
  have hMarks :
      ∀ p : Fin n → Bool,
        prebananaSignatureMark A tupleA p =
          prebananaSignatureMark B tupleB p := by
    intro p
    exact congrFun (congrArg Prod.snd h) p
  calc
    prebananaBooleanParity A (t.evalSet tupleA) =
      ∑ p : Fin n → Bool,
        if t.evalPattern p = true then
          prebananaSignatureMark A tupleA p else 0 :=
        prebananaBooleanTerm_evalParity_eq_profile_sum A tupleA t
    _ = ∑ p : Fin n → Bool,
        if t.evalPattern p = true then
          prebananaSignatureMark B tupleB p else 0 := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [hMarks p]
    _ = prebananaBooleanParity B (t.evalSet tupleB) :=
      (prebananaBooleanTerm_evalParity_eq_profile_sum B tupleB t).symm

end SuccessorTree.NonPrecompact
