import BANANA.NonPrecompact.PrebananaFiniteClass

/-!
# Finite Boolean tuple signatures in pre-BANANA

An n-tuple of Boolean elements determines for each atom the n
membership bits: an element of `Fin n → Bool`. Consequently there
are at most `2 ^ n` distinct realised atom signatures.

The parity marking of each signature fibre is a single F₂ value.
The pair consisting of the realised signatures and their marked
parities belongs to a finite type. These facts are the finite
combinatorial part of the circulation proof that the Fraïssé limit
is oligomorphic. The converse assertion that equal profiles yield
the same orbit uses ultrahomogeneity and the generation of Boolean
subalgebras; it is deliberately not claimed by this file.
-/

namespace SuccessorTree.NonPrecompact

open scoped BigOperators

/-- The membership bits of an atom in an n-tuple of Boolean subsets. -/
def prebananaAtomSignature
    {n : ℕ} (A : PrebananaAtomStructure)
    (tuple : Fin n → Finset (Fin A.atomCount))
    (a : Fin A.atomCount) : Fin n → Bool :=
  fun i => decide (a ∈ tuple i)

/-- Exactly the atom membership signatures realised in this tuple. -/
noncomputable def prebananaRealisedSignatures
    {n : ℕ} (A : PrebananaAtomStructure)
    (tuple : Fin n → Finset (Fin A.atomCount)) :
    Finset (Fin n → Bool) := by
  classical
  exact Finset.univ.image (prebananaAtomSignature A tuple)

/-- The parity of all marked atoms with a specified membership pattern. -/
noncomputable def prebananaSignatureMark
    {n : ℕ} (A : PrebananaAtomStructure)
    (tuple : Fin n → Finset (Fin A.atomCount))
    (pattern : Fin n → Bool) : F2 := by
  classical
  exact ∑ a ∈ (Finset.univ : Finset (Fin A.atomCount)).filter
      (fun a => prebananaAtomSignature A tuple a = pattern), A.mark a

/-- The membership signature records each coordinate faithfully. -/
theorem prebananaAtomSignature_apply_true_iff
    {n : ℕ} (A : PrebananaAtomStructure)
    (tuple : Fin n → Finset (Fin A.atomCount))
    (a : Fin A.atomCount) (i : Fin n) :
    prebananaAtomSignature A tuple a i = true ↔ a ∈ tuple i := by
  simp [prebananaAtomSignature]

/-- An n-tuple distinguishes no more than 2ⁿ kinds of atoms. -/
theorem prebananaRealisedSignatures_card_le_two_pow
    {n : ℕ} (A : PrebananaAtomStructure)
    (tuple : Fin n → Finset (Fin A.atomCount)) :
    (prebananaRealisedSignatures A tuple).card ≤ 2 ^ n := by
  classical
  calc
    (prebananaRealisedSignatures A tuple).card ≤
        (Finset.univ : Finset (Fin n → Bool)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = 2 ^ n := by
      simp [Fintype.card_fun]

/-- An unrealised signature has no atoms and zero marked parity. -/
theorem prebananaSignatureMark_eq_zero_of_not_realised
    {n : ℕ} (A : PrebananaAtomStructure)
    (tuple : Fin n → Finset (Fin A.atomCount))
    (pattern : Fin n → Bool)
    (h : pattern ∉ prebananaRealisedSignatures A tuple) :
    prebananaSignatureMark A tuple pattern = 0 := by
  classical
  unfold prebananaSignatureMark
  apply Finset.sum_eq_zero
  intro a ha
  exfalso
  apply h
  unfold prebananaRealisedSignatures
  apply Finset.mem_image.mpr
  exact ⟨a, Finset.mem_univ _, (Finset.mem_filter.mp ha).2⟩

/-- The finite tuple-profile record: realised membership patterns and
one F₂ mark per pattern. -/
noncomputable def prebananaTupleProfile
    {n : ℕ} (A : PrebananaAtomStructure)
    (tuple : Fin n → Finset (Fin A.atomCount)) :
    Finset (Fin n → Bool) × ((Fin n → Bool) → F2) :=
  ⟨prebananaRealisedSignatures A tuple, prebananaSignatureMark A tuple⟩

/-- For fixed tuple length, the possible finite Boolean parity
profiles form a finite type, independently of the atom count. -/
theorem prebananaTupleProfiles_finite (n : ℕ) :
    Finite (Finset (Fin n → Bool) × ((Fin n → Bool) → F2)) := by
  infer_instance

end SuccessorTree.NonPrecompact
