import BANANA.NonPrecompact.PrebananaGeneratedProfileEquiv

/-!
# Boolean operations on finite generated term ranges

The range of Boolean-term evaluation is a finite Boolean
subalgebra of the ambient atom powerset. We explicitly construct
the constants, complements, unions, intersections and named
generators as elements of the term-value range.

When two tuples have equal complete marked profiles, their
canonical generated-range equivalence transports each term
evaluation to the same term on the other side. We spell out its
preservation of each Boolean operation, so the finite isomorphism
needed for the circulation orbit argument is not left implicit.
-/

namespace SuccessorTree.NonPrecompact

/-- The bottom element of a term-generated Boolean subalgebra. -/
def prebananaTermRange_zero
    {n : ℕ} (A : PrebananaAtomStructure)
    (tuple : Fin n → Finset (Fin A.atomCount)) :
    prebananaTermRange A tuple :=
  ⟨∅, ⟨.zero, rfl⟩⟩

/-- The top element of a term-generated Boolean subalgebra. -/
def prebananaTermRange_one
    {n : ℕ} (A : PrebananaAtomStructure)
    (tuple : Fin n → Finset (Fin A.atomCount)) :
    prebananaTermRange A tuple :=
  ⟨Finset.univ, ⟨.one, rfl⟩⟩

/-- Every distinguished generator lies in its generated algebra. -/
def prebananaTermRange_generator
    {n : ℕ} (A : PrebananaAtomStructure)
    (tuple : Fin n → Finset (Fin A.atomCount))
    (i : Fin n) :
    prebananaTermRange A tuple :=
  ⟨tuple i, ⟨.generator i, rfl⟩⟩

/-- Term values are closed under Boolean complements. -/
noncomputable def prebananaTermRange_complement
    {n : ℕ} (A : PrebananaAtomStructure)
    (tuple : Fin n → Finset (Fin A.atomCount))
    (x : prebananaTermRange A tuple) :
    prebananaTermRange A tuple := by
  classical
  let t := Classical.choose x.property
  have ht : t.evalSet tuple = x.val := Classical.choose_spec x.property
  refine ⟨Finset.univ \ x.val, ⟨.complement t, ?_⟩⟩
  change Finset.univ \ t.evalSet tuple = Finset.univ \ x.val
  rw [ht]

/-- Term values are closed under Boolean joins (finite unions). -/
noncomputable def prebananaTermRange_join
    {n : ℕ} (A : PrebananaAtomStructure)
    (tuple : Fin n → Finset (Fin A.atomCount))
    (x y : prebananaTermRange A tuple) :
    prebananaTermRange A tuple := by
  classical
  let t := Classical.choose x.property
  let u := Classical.choose y.property
  have ht : t.evalSet tuple = x.val := Classical.choose_spec x.property
  have hu : u.evalSet tuple = y.val := Classical.choose_spec y.property
  refine ⟨x.val ∪ y.val, ⟨.join t u, ?_⟩⟩
  change t.evalSet tuple ∪ u.evalSet tuple = x.val ∪ y.val
  rw [ht, hu]

/-- Term values are closed under Boolean meets (finite intersections). -/
noncomputable def prebananaTermRange_meet
    {n : ℕ} (A : PrebananaAtomStructure)
    (tuple : Fin n → Finset (Fin A.atomCount))
    (x y : prebananaTermRange A tuple) :
    prebananaTermRange A tuple := by
  classical
  let t := Classical.choose x.property
  let u := Classical.choose y.property
  have ht : t.evalSet tuple = x.val := Classical.choose_spec x.property
  have hu : u.evalSet tuple = y.val := Classical.choose_spec y.property
  refine ⟨x.val ∩ y.val, ⟨.meet t u, ?_⟩⟩
  change t.evalSet tuple ∩ u.evalSet tuple = x.val ∩ y.val
  rw [ht, hu]

/-- A proof of term representation determines the equivalence image,
even when the source element carries a different existential witness. -/
theorem prebananaGeneratedRangeEquiv_of_term
    {n : ℕ}
    (A B : PrebananaAtomStructure)
    (tupleA : Fin n → Finset (Fin A.atomCount))
    (tupleB : Fin n → Finset (Fin B.atomCount))
    (h : prebananaTupleProfile A tupleA =
      prebananaTupleProfile B tupleB)
    (x : prebananaTermRange A tupleA)
    (t : PrebananaBooleanTerm n)
    (hx : t.evalSet tupleA = x.val) :
    (prebananaGeneratedRangeEquiv_of_profile_eq A B tupleA tupleB h x).val =
      t.evalSet tupleB := by
  have hsub : x =
      (⟨t.evalSet tupleA, ⟨t, rfl⟩⟩ :
        prebananaTermRange A tupleA) := Subtype.ext hx.symm
  rw [hsub]
  exact prebananaGeneratedRangeEquiv_eval_term A B tupleA tupleB h t

/-- The generated-range equivalence preserves the zero constant. -/
theorem prebananaGeneratedRangeEquiv_zero
    {n : ℕ}
    (A B : PrebananaAtomStructure)
    (tupleA : Fin n → Finset (Fin A.atomCount))
    (tupleB : Fin n → Finset (Fin B.atomCount))
    (h : prebananaTupleProfile A tupleA =
      prebananaTupleProfile B tupleB) :
    (prebananaGeneratedRangeEquiv_of_profile_eq A B tupleA tupleB h
      (prebananaTermRange_zero A tupleA)).val = ∅ := by
  exact prebananaGeneratedRangeEquiv_of_term A B tupleA tupleB h
    (prebananaTermRange_zero A tupleA) .zero rfl

/-- The generated-range equivalence preserves the unit constant. -/
theorem prebananaGeneratedRangeEquiv_one
    {n : ℕ}
    (A B : PrebananaAtomStructure)
    (tupleA : Fin n → Finset (Fin A.atomCount))
    (tupleB : Fin n → Finset (Fin B.atomCount))
    (h : prebananaTupleProfile A tupleA =
      prebananaTupleProfile B tupleB) :
    (prebananaGeneratedRangeEquiv_of_profile_eq A B tupleA tupleB h
      (prebananaTermRange_one A tupleA)).val = Finset.univ := by
  exact prebananaGeneratedRangeEquiv_of_term A B tupleA tupleB h
    (prebananaTermRange_one A tupleA) .one rfl

/-- The generated-range equivalence sends each named generator to
the corresponding generator of the second tuple. -/
theorem prebananaGeneratedRangeEquiv_generator
    {n : ℕ}
    (A B : PrebananaAtomStructure)
    (tupleA : Fin n → Finset (Fin A.atomCount))
    (tupleB : Fin n → Finset (Fin B.atomCount))
    (h : prebananaTupleProfile A tupleA =
      prebananaTupleProfile B tupleB)
    (i : Fin n) :
    (prebananaGeneratedRangeEquiv_of_profile_eq A B tupleA tupleB h
      (prebananaTermRange_generator A tupleA i)).val = tupleB i := by
  exact prebananaGeneratedRangeEquiv_of_term A B tupleA tupleB h
    (prebananaTermRange_generator A tupleA i) (.generator i) rfl

/-- Boolean complementation is respected. -/
theorem prebananaGeneratedRangeEquiv_complement
    {n : ℕ}
    (A B : PrebananaAtomStructure)
    (tupleA : Fin n → Finset (Fin A.atomCount))
    (tupleB : Fin n → Finset (Fin B.atomCount))
    (h : prebananaTupleProfile A tupleA =
      prebananaTupleProfile B tupleB)
    (x : prebananaTermRange A tupleA) :
    (prebananaGeneratedRangeEquiv_of_profile_eq A B tupleA tupleB h
      (prebananaTermRange_complement A tupleA x)).val =
    Finset.univ \
      (prebananaGeneratedRangeEquiv_of_profile_eq A B tupleA tupleB h x).val := by
  classical
  obtain ⟨t, ht⟩ := x.property
  have hcomplement :
      (PrebananaBooleanTerm.complement t).evalSet tupleA =
        (prebananaTermRange_complement A tupleA x).val := by
    change Finset.univ \ t.evalSet tupleA = Finset.univ \ x.val
    rw [ht]
  calc
    (prebananaGeneratedRangeEquiv_of_profile_eq A B tupleA tupleB h
       (prebananaTermRange_complement A tupleA x)).val =
        (PrebananaBooleanTerm.complement t).evalSet tupleB :=
      prebananaGeneratedRangeEquiv_of_term A B tupleA tupleB h _ _ hcomplement
    _ = Finset.univ \ t.evalSet tupleB := rfl
    _ = Finset.univ \
        (prebananaGeneratedRangeEquiv_of_profile_eq A B tupleA tupleB h x).val := by
      rw [prebananaGeneratedRangeEquiv_of_term A B tupleA tupleB h x t ht]

/-- Boolean joins are respected. -/
theorem prebananaGeneratedRangeEquiv_join
    {n : ℕ}
    (A B : PrebananaAtomStructure)
    (tupleA : Fin n → Finset (Fin A.atomCount))
    (tupleB : Fin n → Finset (Fin B.atomCount))
    (h : prebananaTupleProfile A tupleA =
      prebananaTupleProfile B tupleB)
    (x y : prebananaTermRange A tupleA) :
    (prebananaGeneratedRangeEquiv_of_profile_eq A B tupleA tupleB h
      (prebananaTermRange_join A tupleA x y)).val =
    (prebananaGeneratedRangeEquiv_of_profile_eq A B tupleA tupleB h x).val ∪
      (prebananaGeneratedRangeEquiv_of_profile_eq A B tupleA tupleB h y).val := by
  classical
  obtain ⟨t, ht⟩ := x.property
  obtain ⟨u, hu⟩ := y.property
  have hjoin :
      (PrebananaBooleanTerm.join t u).evalSet tupleA =
        (prebananaTermRange_join A tupleA x y).val := by
    change t.evalSet tupleA ∪ u.evalSet tupleA = x.val ∪ y.val
    rw [ht, hu]
  calc
    (prebananaGeneratedRangeEquiv_of_profile_eq A B tupleA tupleB h
      (prebananaTermRange_join A tupleA x y)).val =
        (PrebananaBooleanTerm.join t u).evalSet tupleB :=
      prebananaGeneratedRangeEquiv_of_term A B tupleA tupleB h _ _ hjoin
    _ = t.evalSet tupleB ∪ u.evalSet tupleB := rfl
    _ = (prebananaGeneratedRangeEquiv_of_profile_eq A B tupleA tupleB h x).val ∪
        (prebananaGeneratedRangeEquiv_of_profile_eq A B tupleA tupleB h y).val := by
      rw [prebananaGeneratedRangeEquiv_of_term A B tupleA tupleB h x t ht,
        prebananaGeneratedRangeEquiv_of_term A B tupleA tupleB h y u hu]

/-- Boolean meets are respected. -/
theorem prebananaGeneratedRangeEquiv_meet
    {n : ℕ}
    (A B : PrebananaAtomStructure)
    (tupleA : Fin n → Finset (Fin A.atomCount))
    (tupleB : Fin n → Finset (Fin B.atomCount))
    (h : prebananaTupleProfile A tupleA =
      prebananaTupleProfile B tupleB)
    (x y : prebananaTermRange A tupleA) :
    (prebananaGeneratedRangeEquiv_of_profile_eq A B tupleA tupleB h
      (prebananaTermRange_meet A tupleA x y)).val =
    (prebananaGeneratedRangeEquiv_of_profile_eq A B tupleA tupleB h x).val ∩
      (prebananaGeneratedRangeEquiv_of_profile_eq A B tupleA tupleB h y).val := by
  classical
  obtain ⟨t, ht⟩ := x.property
  obtain ⟨u, hu⟩ := y.property
  have hmeet :
      (PrebananaBooleanTerm.meet t u).evalSet tupleA =
        (prebananaTermRange_meet A tupleA x y).val := by
    change t.evalSet tupleA ∩ u.evalSet tupleA = x.val ∩ y.val
    rw [ht, hu]
  calc
    (prebananaGeneratedRangeEquiv_of_profile_eq A B tupleA tupleB h
      (prebananaTermRange_meet A tupleA x y)).val =
        (PrebananaBooleanTerm.meet t u).evalSet tupleB :=
      prebananaGeneratedRangeEquiv_of_term A B tupleA tupleB h _ _ hmeet
    _ = t.evalSet tupleB ∩ u.evalSet tupleB := rfl
    _ = (prebananaGeneratedRangeEquiv_of_profile_eq A B tupleA tupleB h x).val ∩
        (prebananaGeneratedRangeEquiv_of_profile_eq A B tupleA tupleB h y).val := by
      rw [prebananaGeneratedRangeEquiv_of_term A B tupleA tupleB h x t ht,
        prebananaGeneratedRangeEquiv_of_term A B tupleA tupleB h y u hu]

end SuccessorTree.NonPrecompact
