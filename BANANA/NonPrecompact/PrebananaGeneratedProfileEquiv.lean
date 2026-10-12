import BANANA.NonPrecompact.PrebananaTupleTermEqualities
import BANANA.NonPrecompact.PrebananaTupleTermParity
import BANANA.NonPrecompact.PrebananaGeneratedTermRange

/-!
# Generated finite marked Boolean term ranges from tuple profiles

A complete finite tuple profile determines all Boolean-term
equalities and all F₂ marks of term evaluations. Combining these
two kernel-checked finite facts with the generic equivalence of
generated term ranges gives a bijection on the values of all
terms which also preserves their marking.

The map sends the evaluation of every term on the first tuple
to the evaluation of the same term on the second tuple. This is
the concrete term-level algebraic bridge needed for the
circulation proof of oligomorphicity. The final extension by
homogeneity and Ryll--Nardzewski remain separate.
-/

namespace SuccessorTree.NonPrecompact

/-- Equal complete tuple profiles induce an equivalence between
the sets of values of Boolean terms in their respective tuples. -/
noncomputable def prebananaGeneratedRangeEquiv_of_profile_eq
    {n : ℕ}
    (A B : PrebananaAtomStructure)
    (tupleA : Fin n → Finset (Fin A.atomCount))
    (tupleB : Fin n → Finset (Fin B.atomCount))
    (h : prebananaTupleProfile A tupleA =
      prebananaTupleProfile B tupleB) :
    prebananaTermRange A tupleA ≃
      prebananaTermRange B tupleB :=
  prebananaTermRangeEquiv_of_equalities A B tupleA tupleB
    (fun t u =>
      prebananaBooleanTerm_equalities_of_profile_eq
        A B tupleA tupleB h t u)

/-- The induced equivalence preserves the marking of every
generated Boolean term value. -/
theorem prebananaGeneratedRangeEquiv_parity_of_profile_eq
    {n : ℕ}
    (A B : PrebananaAtomStructure)
    (tupleA : Fin n → Finset (Fin A.atomCount))
    (tupleB : Fin n → Finset (Fin B.atomCount))
    (h : prebananaTupleProfile A tupleA =
      prebananaTupleProfile B tupleB)
    (x : prebananaTermRange A tupleA) :
    prebananaBooleanParity B
      ((prebananaGeneratedRangeEquiv_of_profile_eq
        A B tupleA tupleB h x).val) =
      prebananaBooleanParity A x.val := by
  exact prebananaTermRangeEquiv_preserves_parity A B tupleA tupleB
    (fun t u =>
      prebananaBooleanTerm_equalities_of_profile_eq
        A B tupleA tupleB h t u)
    (fun t =>
      prebananaBooleanTerm_parity_of_profile_eq
        A B tupleA tupleB h t)
    x

/-- Term naturality: the equivalence sends the interpretation
of each finite Boolean term to that of the identical term in
the second tuple. In particular it preserves the named
generators and the operations whenever applied to term values. -/
theorem prebananaGeneratedRangeEquiv_eval_term
    {n : ℕ}
    (A B : PrebananaAtomStructure)
    (tupleA : Fin n → Finset (Fin A.atomCount))
    (tupleB : Fin n → Finset (Fin B.atomCount))
    (h : prebananaTupleProfile A tupleA =
      prebananaTupleProfile B tupleB)
    (t : PrebananaBooleanTerm n) :
    (prebananaGeneratedRangeEquiv_of_profile_eq
      A B tupleA tupleB h
      ⟨t.evalSet tupleA, ⟨t, rfl⟩⟩).val =
      t.evalSet tupleB := by
  classical
  let x : prebananaTermRange A tupleA :=
    ⟨t.evalSet tupleA, ⟨t, rfl⟩⟩
  have hx :
      (Classical.choose x.property).evalSet tupleA =
        t.evalSet tupleA := Classical.choose_spec x.property
  change (Classical.choose x.property).evalSet tupleB =
    t.evalSet tupleB
  exact (prebananaBooleanTerm_equalities_of_profile_eq
    A B tupleA tupleB h _ t).mp hx

end SuccessorTree.NonPrecompact
