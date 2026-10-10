import BANANA.NonPrecompact.CompletionAutomorphism
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Simultaneous extension of total actions to canonical perfect completions

Every finite two-sorted BANANA self-embedding is an automorphism:
on each finite coordinate sort, injectivity implies surjectivity.

Any finite family of such automorphisms preserves the original
arbitrary (possibly degenerate) pairing. The canonical completion
construction therefore extends them, one by one, to automorphisms of
*one and the same* finite perfect pairing.

This is the final completion step for an equivariant finite-system
amalgam. No amalgamation claim is made in this module itself.
-/

namespace SuccessorTree.NonPrecompact

namespace BananaMatrixEmbedding

/-- The left sort of a finite BANANA self-embedding is bijective. -/
noncomputable def arbitrarySelfLeftEquiv
    {l r : ℕ} {A : BananaMatrixStructure l r}
    (H : BananaMatrixEmbedding A A) :
    (Fin l → F2) ≃ₗ[F2] (Fin l → F2) :=
  LinearEquiv.ofBijective H.left
    ⟨H.left_injective,
      Finite.injective_iff_surjective.mp H.left_injective⟩

/-- The right sort of a finite BANANA self-embedding is bijective. -/
noncomputable def arbitrarySelfRightEquiv
    {l r : ℕ} {A : BananaMatrixStructure l r}
    (H : BananaMatrixEmbedding A A) :
    (Fin r → F2) ≃ₗ[F2] (Fin r → F2) :=
  LinearEquiv.ofBijective H.right
    ⟨H.right_injective,
      Finite.injective_iff_surjective.mp H.right_injective⟩

@[simp] theorem arbitrarySelfLeftEquiv_apply
    {l r : ℕ} {A : BananaMatrixStructure l r}
    (H : BananaMatrixEmbedding A A) (x : Fin l → F2) :
    H.arbitrarySelfLeftEquiv x = H.left x := rfl

@[simp] theorem arbitrarySelfRightEquiv_apply
    {l r : ℕ} {A : BananaMatrixStructure l r}
    (H : BananaMatrixEmbedding A A) (y : Fin r → F2) :
    H.arbitrarySelfRightEquiv y = H.right y := rfl

end BananaMatrixEmbedding

/-- Extend all n total BANANA automorphisms of a finite pairing
to automorphisms of its common canonical perfect completion,
simultaneously on both sorts. -/
theorem exists_bananaTotalFamily_commonPerfectCompletion
    {n l r : ℕ}
    (A : BananaMatrixStructure l r)
    (H : Fin n → BananaMatrixEmbedding A A) :
    ∃ K : Fin n →
      BananaMatrixEmbedding
        (perfectBanana (l + r)) (perfectBanana (l + r)),
      (∀ i (x : Fin l → F2),
        (K i).left (A.completionLeft x) =
          A.completionLeft ((H i).left x)) ∧
      (∀ i (y : Fin r → F2),
        (K i).right (A.completionRight y) =
          A.completionRight ((H i).right y)) := by
  classical
  let K : Fin n →
      BananaMatrixEmbedding
        (perfectBanana (l + r)) (perfectBanana (l + r)) :=
    fun i => BananaMatrixStructure.completionAutomorphism
      (H i).arbitrarySelfLeftEquiv
      (H i).arbitrarySelfRightEquiv
  refine ⟨K, ?_, ?_⟩
  · intro i x
    change
      (BananaMatrixStructure.completionAutomorphism
        (H i).arbitrarySelfLeftEquiv
        (H i).arbitrarySelfRightEquiv).left
          (A.completionLeft x) =
        A.completionLeft ((H i).left x)
    simpa only [BananaMatrixEmbedding.arbitrarySelfLeftEquiv_apply] using
      A.completionAutomorphism_left_completion
        (H i).arbitrarySelfLeftEquiv
        (H i).arbitrarySelfRightEquiv x
  · intro i y
    have hpair :
        ∀ x y, A.eval ((H i).arbitrarySelfLeftEquiv x)
          ((H i).arbitrarySelfRightEquiv y) = A.eval x y := by
      intro x z
      simpa only [BananaMatrixEmbedding.arbitrarySelfLeftEquiv_apply,
        BananaMatrixEmbedding.arbitrarySelfRightEquiv_apply] using
          (H i).pairing_apply x z
    change
      (BananaMatrixStructure.completionAutomorphism
        (H i).arbitrarySelfLeftEquiv
        (H i).arbitrarySelfRightEquiv).right
          (A.completionRight y) =
        A.completionRight ((H i).right y)
    simpa only [BananaMatrixEmbedding.arbitrarySelfRightEquiv_apply] using
      A.completionAutomorphism_right_completion
        (H i).arbitrarySelfLeftEquiv
        (H i).arbitrarySelfRightEquiv hpair y

end SuccessorTree.NonPrecompact
