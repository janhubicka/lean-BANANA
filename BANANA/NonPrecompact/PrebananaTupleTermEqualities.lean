import BANANA.NonPrecompact.PrebananaBooleanTerms
import BANANA.NonPrecompact.PrebananaTupleSignatureEmbedding

/-!
# Boolean-term equalities are determined by finite tuple profiles

The finite pre-BANANA tuple profile records which membership patterns
are realised, together with the parity of the fibre of each pattern.
The realised-pattern component alone already determines all equations
between Boolean terms evaluated at a distinguished tuple.

This is a concrete, finite part of the passage from tuple profiles to
isomorphisms of finitely generated subalgebras; it does not itself
prove a Fraïssé-limit orbit classification.
-/

namespace SuccessorTree.NonPrecompact

/-- Two Boolean terms agree on a finite tuple precisely when their
truth functions agree on every realised atom membership pattern. -/
theorem prebananaBooleanTerm_evalSet_eq_iff_patterns
    {n : ℕ}
    (A : PrebananaAtomStructure)
    (tuple : Fin n → Finset (Fin A.atomCount))
    (t u : PrebananaBooleanTerm n) :
    t.evalSet tuple = u.evalSet tuple ↔
      ∀ p ∈ prebananaRealisedSignatures A tuple,
        t.evalPattern p = u.evalPattern p := by
  classical
  constructor
  · intro heq p hp
    change p ∈ (Finset.univ : Finset (Fin A.atomCount)).image
      (prebananaAtomSignature A tuple) at hp
    obtain ⟨a, _, hpa⟩ := Finset.mem_image.mp hp
    have hmem : a ∈ t.evalSet tuple ↔ a ∈ u.evalSet tuple := by
      rw [heq]
    rw [t.mem_evalSet_iff_pattern A tuple a,
      u.mem_evalSet_iff_pattern A tuple a, hpa] at hmem
    cases ht : t.evalPattern p <;>
      cases hu : u.evalPattern p <;> simp_all
  · intro hpattern
    apply Finset.ext
    intro a
    have hp : prebananaAtomSignature A tuple a ∈
        prebananaRealisedSignatures A tuple := by
      change prebananaAtomSignature A tuple a ∈
        (Finset.univ : Finset (Fin A.atomCount)).image
          (prebananaAtomSignature A tuple)
      exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
    rw [t.mem_evalSet_iff_pattern A tuple a,
      u.mem_evalSet_iff_pattern A tuple a, hpattern _ hp]

/-- Equality of complete tuple profiles determines the truth of
every equation between Boolean terms in the generators. -/
theorem prebananaBooleanTerm_equalities_of_profile_eq
    {n : ℕ}
    (A B : PrebananaAtomStructure)
    (tupleA : Fin n → Finset (Fin A.atomCount))
    (tupleB : Fin n → Finset (Fin B.atomCount))
    (h : prebananaTupleProfile A tupleA =
      prebananaTupleProfile B tupleB)
    (t u : PrebananaBooleanTerm n) :
    (t.evalSet tupleA = u.evalSet tupleA) ↔
      (t.evalSet tupleB = u.evalSet tupleB) := by
  have hRealised :
      prebananaRealisedSignatures A tupleA =
      prebananaRealisedSignatures B tupleB :=
    congrArg Prod.fst h
  rw [prebananaBooleanTerm_evalSet_eq_iff_patterns A tupleA t u,
    prebananaBooleanTerm_evalSet_eq_iff_patterns B tupleB t u,
    hRealised]

end SuccessorTree.NonPrecompact
