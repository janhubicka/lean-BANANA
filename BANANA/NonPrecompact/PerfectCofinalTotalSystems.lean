import BANANA.NonPrecompact.PerfectFamilyExtension
import BANANA.NonPrecompact.Completion

/-!
# Cofinal perfect total extensions of finite BANANA n-systems

A finite system of n partial isomorphisms is represented by an
underlying finite pairing A and, for each i<n, two embeddings of
a finite source D_i into A. The two copies give the domain and
range of the i-th partial isomorphism.

First embed A into its explicit perfect completion B_(l+r).
The finite-family homogeneity theorem then extends all the
partial isomorphisms to total automorphisms of this *same*
perfect completion.

The precise system category and JEP/WAP transfer are subsequent
formalisation tasks; this lemma verifies the cofinal completion
construction without introducing that categorical infrastructure.
-/

namespace SuccessorTree.NonPrecompact

/-- All members of a finite family of partial isomorphisms of a
finite BANANA pairing become total automorphisms of one common
perfect completion of that pairing. -/
theorem exists_common_perfect_completion_total_family
    {n l r : ℕ}
    (A : BananaMatrixStructure l r)
    (dl dr : Fin n → ℕ)
    (D : ∀ i : Fin n, BananaMatrixStructure (dl i) (dr i))
    (e₁ e₂ : ∀ i : Fin n, BananaMatrixEmbedding (D i) A) :
    ∃ f : BananaMatrixEmbedding A (perfectBanana (l + r)),
    ∃ H : Fin n →
        BananaMatrixEmbedding
          (perfectBanana (l + r))
          (perfectBanana (l + r)),
      (∀ i (x : Fin (dl i) → F2),
        (H i).left (f.left ((e₁ i).left x)) =
          f.left ((e₂ i).left x)) ∧
      (∀ i (y : Fin (dr i) → F2),
        (H i).right (f.right ((e₁ i).right y)) =
          f.right ((e₂ i).right y)) := by
  let f := A.completionEmbedding
  let leftCopies : ∀ i : Fin n,
      BananaMatrixEmbedding (D i) (perfectBanana (l + r)) :=
    fun i => BananaMatrixEmbedding.comp f (e₁ i)
  let rightCopies : ∀ i : Fin n,
      BananaMatrixEmbedding (D i) (perfectBanana (l + r)) :=
    fun i => BananaMatrixEmbedding.comp f (e₂ i)
  obtain ⟨H, hL, hR⟩ :=
    exists_perfectPairAutomorphism_family_extends
      dl dr D leftCopies rightCopies
  refine ⟨f, H, ?_, ?_⟩
  · intro i x
    simpa only [leftCopies, rightCopies,
      BananaMatrixEmbedding.comp, LinearMap.comp_apply] using hL i x
  · intro i y
    simpa only [leftCopies, rightCopies,
      BananaMatrixEmbedding.comp, LinearMap.comp_apply] using hR i y

end SuccessorTree.NonPrecompact
