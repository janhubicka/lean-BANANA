import BANANA.NonPrecompact.PrebananaGeneratedBooleanOperations

/-!
# Finite generated marked Boolean isomorphisms from tuple profiles

We package the operation-preserving equivalence between finite
Boolean-term evaluation ranges as one explicit structure. This makes
precise the finite generated-subalgebra isomorphism needed for the
circulation argument: the correspondence preserves both Boolean
operations and the F₂-valued marking, and sends each distinguished
generator to its counterpart.

The countable Fraïssé limit, extension of partial isomorphisms
to automorphisms, and the Ryll--Nardzewski implication are not
asserted by this file.
-/

namespace SuccessorTree.NonPrecompact

/-- An isomorphism of the finite marked Boolean algebras generated
by two tuples, recorded using their concrete term-value ranges. -/
structure PrebananaGeneratedMarkedIso
    {n : ℕ} (A B : PrebananaAtomStructure)
    (tupleA : Fin n → Finset (Fin A.atomCount))
    (tupleB : Fin n → Finset (Fin B.atomCount)) where
  equiv : prebananaTermRange A tupleA ≃ prebananaTermRange B tupleB
  map_zero :
    (equiv (prebananaTermRange_zero A tupleA)).val = ∅
  map_one :
    (equiv (prebananaTermRange_one A tupleA)).val = Finset.univ
  map_generator : ∀ i : Fin n,
    (equiv (prebananaTermRange_generator A tupleA i)).val = tupleB i
  map_complement : ∀ x : prebananaTermRange A tupleA,
    (equiv (prebananaTermRange_complement A tupleA x)).val =
      Finset.univ \ (equiv x).val
  map_join : ∀ x y : prebananaTermRange A tupleA,
    (equiv (prebananaTermRange_join A tupleA x y)).val =
      (equiv x).val ∪ (equiv y).val
  map_meet : ∀ x y : prebananaTermRange A tupleA,
    (equiv (prebananaTermRange_meet A tupleA x y)).val =
      (equiv x).val ∩ (equiv y).val
  map_mark : ∀ x : prebananaTermRange A tupleA,
    prebananaBooleanParity B (equiv x).val =
      prebananaBooleanParity A x.val

/-- Every equality of complete finite tuple profiles induces a
mark-preserving isomorphism of the tuple-generated Boolean algebras,
compatible with each distinguished tuple coordinate. -/
noncomputable def prebananaGeneratedMarkedIso_of_profile_eq
    {n : ℕ} (A B : PrebananaAtomStructure)
    (tupleA : Fin n → Finset (Fin A.atomCount))
    (tupleB : Fin n → Finset (Fin B.atomCount))
    (h : prebananaTupleProfile A tupleA =
      prebananaTupleProfile B tupleB) :
    PrebananaGeneratedMarkedIso A B tupleA tupleB where
  equiv := prebananaGeneratedRangeEquiv_of_profile_eq A B tupleA tupleB h
  map_zero := prebananaGeneratedRangeEquiv_zero A B tupleA tupleB h
  map_one := prebananaGeneratedRangeEquiv_one A B tupleA tupleB h
  map_generator := prebananaGeneratedRangeEquiv_generator A B tupleA tupleB h
  map_complement := prebananaGeneratedRangeEquiv_complement A B tupleA tupleB h
  map_join := prebananaGeneratedRangeEquiv_join A B tupleA tupleB h
  map_meet := prebananaGeneratedRangeEquiv_meet A B tupleA tupleB h
  map_mark := prebananaGeneratedRangeEquiv_parity_of_profile_eq A B tupleA tupleB h

/-- The inverse isomorphism also preserves the F₂ marking. -/
theorem PrebananaGeneratedMarkedIso.symm_preserves_mark
    {n : ℕ} {A B : PrebananaAtomStructure}
    {tupleA : Fin n → Finset (Fin A.atomCount)}
    {tupleB : Fin n → Finset (Fin B.atomCount)}
    (e : PrebananaGeneratedMarkedIso A B tupleA tupleB)
    (y : prebananaTermRange B tupleB) :
    prebananaBooleanParity A (e.equiv.symm y).val =
      prebananaBooleanParity B y.val := by
  have he := e.map_mark (e.equiv.symm y)
  simpa using he.symm

end SuccessorTree.NonPrecompact
