import BANANA.NonPrecompact.PrebananaBooleanTerms
import BANANA.NonPrecompact.PrebananaPowersetBridge

/-!
# Equivalence of finitely generated Boolean term ranges

An n-tuple of elements of a finite Boolean algebra generates exactly
the values of Boolean terms in those n variables. This module
constructs the equivalence between the two sets of term values when
the two evaluations have the same equality kernel.

The construction is independent of the way equality of term values
was established. In a later bridge, equality of finite tuple profiles
supplies this hypothesis. A separate parity hypothesis gives a
mark-preserving equivalence.
-/

namespace SuccessorTree.NonPrecompact

/-- Values of Boolean terms in a fixed finite tuple, represented
as a subtype of the ambient Boolean powerset. -/
def prebananaTermRange
    {n : ℕ} (A : PrebananaAtomStructure)
    (tuple : Fin n → Finset (Fin A.atomCount)) : Type :=
  { s : Finset (Fin A.atomCount) //
    ∃ t : PrebananaBooleanTerm n, t.evalSet tuple = s }

/-- Equal term-equality kernels produce a canonical equivalence
between the two sets of values of terms. The map is well defined:
different representatives of a source value represent the same
target value, because term equality transfers in both directions. -/
noncomputable def prebananaTermRangeEquiv_of_equalities
    {n : ℕ} (A B : PrebananaAtomStructure)
    (tupleA : Fin n → Finset (Fin A.atomCount))
    (tupleB : Fin n → Finset (Fin B.atomCount))
    (hEq : ∀ t u : PrebananaBooleanTerm n,
      (t.evalSet tupleA = u.evalSet tupleA) ↔
      (t.evalSet tupleB = u.evalSet tupleB)) :
    prebananaTermRange A tupleA ≃ prebananaTermRange B tupleB := by
  classical
  let toB (x : prebananaTermRange A tupleA) :
      prebananaTermRange B tupleB :=
    ⟨(Classical.choose x.property).evalSet tupleB,
      ⟨Classical.choose x.property, rfl⟩⟩
  let toA (y : prebananaTermRange B tupleB) :
      prebananaTermRange A tupleA :=
    ⟨(Classical.choose y.property).evalSet tupleA,
      ⟨Classical.choose y.property, rfl⟩⟩
  refine {
    toFun := toB
    invFun := toA
    left_inv := ?_
    right_inv := ?_
  }
  · intro x
    apply Subtype.ext
    change (Classical.choose (toB x).property).evalSet tupleA = x.val
    have hB :
        (Classical.choose (toB x).property).evalSet tupleB =
          (Classical.choose x.property).evalSet tupleB :=
      Classical.choose_spec (toB x).property
    have hA := (hEq _ _).mpr hB
    exact hA.trans (Classical.choose_spec x.property)
  · intro y
    apply Subtype.ext
    change (Classical.choose (toA y).property).evalSet tupleB = y.val
    have hA :
        (Classical.choose (toA y).property).evalSet tupleA =
          (Classical.choose y.property).evalSet tupleA :=
      Classical.choose_spec (toA y).property
    have hB := (hEq _ _).mp hA
    exact hB.trans (Classical.choose_spec y.property)

/-- If corresponding terms also have equal parity, the
term-range equivalence preserves the marking on each value. -/
theorem prebananaTermRangeEquiv_preserves_parity
    {n : ℕ} (A B : PrebananaAtomStructure)
    (tupleA : Fin n → Finset (Fin A.atomCount))
    (tupleB : Fin n → Finset (Fin B.atomCount))
    (hEq : ∀ t u : PrebananaBooleanTerm n,
      (t.evalSet tupleA = u.evalSet tupleA) ↔
      (t.evalSet tupleB = u.evalSet tupleB))
    (hMark : ∀ t : PrebananaBooleanTerm n,
      prebananaBooleanParity A (t.evalSet tupleA) =
      prebananaBooleanParity B (t.evalSet tupleB))
    (x : prebananaTermRange A tupleA) :
    prebananaBooleanParity B
      ((prebananaTermRangeEquiv_of_equalities A B tupleA tupleB hEq x).val) =
    prebananaBooleanParity A x.val := by
  classical
  let t := Classical.choose x.property
  have ht : t.evalSet tupleA = x.val :=
    Classical.choose_spec x.property
  change prebananaBooleanParity B (t.evalSet tupleB) =
    prebananaBooleanParity A x.val
  exact (hMark t).symm.trans (congrArg (prebananaBooleanParity A) ht)

end SuccessorTree.NonPrecompact
