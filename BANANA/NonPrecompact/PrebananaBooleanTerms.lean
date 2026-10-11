import BANANA.NonPrecompact.PrebananaTupleSignatures

/-!
# Boolean terms depend only on atom membership signatures

An n-tuple of Boolean elements generates a Boolean subalgebra.
Every element of that subalgebra is obtained by evaluating a
Boolean term in the n generators.

The truth of any such term on an ambient atom depends only on
its n-bit membership signature. Consequently two ambient atoms
with the same signature cannot be distinguished by any Boolean
term in the generators.

This is a syntactic component of the circulation argument
for omega-categoricity. Combining it with equality and parity
of the finite signature profiles and ultrahomogeneity is a
separate step; no classification of orbits is claimed here.
-/

namespace SuccessorTree.NonPrecompact

/-- Finite Boolean terms over n named generators. -/
inductive PrebananaBooleanTerm (n : ℕ) : Type where
  | zero : PrebananaBooleanTerm n
  | one : PrebananaBooleanTerm n
  | generator : Fin n → PrebananaBooleanTerm n
  | complement : PrebananaBooleanTerm n → PrebananaBooleanTerm n
  | join : PrebananaBooleanTerm n → PrebananaBooleanTerm n → PrebananaBooleanTerm n
  | meet : PrebananaBooleanTerm n → PrebananaBooleanTerm n → PrebananaBooleanTerm n

/-- Evaluate a Boolean term at actual finite subsets of atoms. -/
def PrebananaBooleanTerm.evalSet
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (tuple : Fin n → Finset ι) : PrebananaBooleanTerm n → Finset ι
  | .zero => ∅
  | .one => Finset.univ
  | .generator i => tuple i
  | .complement t => Finset.univ \ evalSet tuple t
  | .join t u => evalSet tuple t ∪ evalSet tuple u
  | .meet t u => evalSet tuple t ∩ evalSet tuple u

/-- Evaluate the same term on a single n-bit atom signature. -/
def PrebananaBooleanTerm.evalPattern
    {n : ℕ} (pattern : Fin n → Bool) : PrebananaBooleanTerm n → Bool
  | .zero => false
  | .one => true
  | .generator i => pattern i
  | .complement t => !(evalPattern pattern t)
  | .join t u => evalPattern pattern t || evalPattern pattern u
  | .meet t u => evalPattern pattern t && evalPattern pattern u

/-- An atom satisfies a Boolean term exactly when its membership
signature satisfies the corresponding Boolean truth-function. -/
theorem PrebananaBooleanTerm.mem_evalSet_iff_pattern
    {n : ℕ} (A : PrebananaAtomStructure)
    (tuple : Fin n → Finset (Fin A.atomCount))
    (a : Fin A.atomCount)
    (t : PrebananaBooleanTerm n) :
    a ∈ t.evalSet tuple ↔
      t.evalPattern (prebananaAtomSignature A tuple a) = true := by
  induction t with
  | zero =>
      simp [evalSet, evalPattern]
  | one =>
      simp [evalSet, evalPattern]
  | generator i =>
      simpa [evalSet, evalPattern] using
        (prebananaAtomSignature_apply_true_iff A tuple a i).symm
  | complement t ih =>
      simp [evalSet, evalPattern, ih]
  | join t u iht ihu =>
      simp [evalSet, evalPattern, iht, ihu]
  | meet t u iht ihu =>
      simp [evalSet, evalPattern, iht, ihu]

/-- Two atoms having the same n-bit signature belong to exactly
the same Boolean-term evaluations in the distinguished tuple. -/
theorem PrebananaBooleanTerm.mem_evalSet_iff_of_same_signature
    {n : ℕ} (A : PrebananaAtomStructure)
    (tuple : Fin n → Finset (Fin A.atomCount))
    (a b : Fin A.atomCount)
    (h : prebananaAtomSignature A tuple a =
      prebananaAtomSignature A tuple b)
    (t : PrebananaBooleanTerm n) :
    a ∈ t.evalSet tuple ↔ b ∈ t.evalSet tuple := by
  rw [t.mem_evalSet_iff_pattern A tuple a,
      t.mem_evalSet_iff_pattern A tuple b, h]

end SuccessorTree.NonPrecompact
