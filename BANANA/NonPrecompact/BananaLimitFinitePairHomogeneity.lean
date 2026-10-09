import BANANA.NonPrecompact.BananaLimitFiniteEmbeddingFactor
import BANANA.NonPrecompact.PerfectSelfEmbedding

/-!
# Matching two finite limit embeddings inside a perfect coordinate block

The finite perfect-pair homogeneity theorem already proves that any two
embeddings of a finite BANANA structure into the *same* finite standard
perfect pair are carried one to the other by a finite pairing
automorphism. This module combines it with finite-support
factorisation for the explicit countable BANANA limit.

The separate next step extends the resulting finite perfect-block
automorphism by the identity outside its coordinate support.
-/

namespace SuccessorTree.NonPrecompact

open scoped Matrix

namespace BananaMatrixEmbeddingToLimit

/-- Two embeddings of the same finite BANANA structure into the explicit
countable pairing are conjugate inside one common finite perfect block.
The equalities give exact pointwise recovery on both sorts. -/
theorem exists_finite_perfect_ambient_automorphism
    {l r : ℕ} {A : BananaMatrixStructure l r}
    (e₁ e₂ : BananaMatrixEmbeddingToLimit A) :
    ∃ S : Finset ℚ,
      ∃ f₁ f₂ : BananaMatrixEmbedding A (perfectBanana S.card),
        ∃ H : BananaMatrixEmbedding
            (perfectBanana S.card) (perfectBanana S.card),
          (∀ x, (bananaLimitBlockStandardEmbedding S).left (f₁.left x) =
            e₁.left x) ∧
          (∀ y, (bananaLimitBlockStandardEmbedding S).right (f₁.right y) =
            e₁.right y) ∧
          (∀ x, (bananaLimitBlockStandardEmbedding S).left (f₂.left x) =
            e₂.left x) ∧
          (∀ y, (bananaLimitBlockStandardEmbedding S).right (f₂.right y) =
            e₂.right y) ∧
          (∀ x, H.left (f₁.left x) = f₂.left x) ∧
          (∀ y, H.right (f₁.right y) = f₂.right y) := by
  classical
  obtain ⟨S, h₁L, h₁R, h₂L, h₂R⟩ :=
    exists_common_finite_block e₁ e₂
  let f₁ := e₁.factorToPerfectBlock S h₁L h₁R
  let f₂ := e₂.factorToPerfectBlock S h₂L h₂R
  obtain ⟨H, hL, hR⟩ :=
    exists_perfectPairAutomorphism_extends f₁ f₂
  refine ⟨S, f₁, f₂, H, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact e₁.factorToPerfectBlock_left S h₁L h₁R
  · exact e₁.factorToPerfectBlock_right S h₁L h₁R
  · exact e₂.factorToPerfectBlock_left S h₂L h₂R
  · exact e₂.factorToPerfectBlock_right S h₂L h₂R
  · exact hL
  · exact hR

end BananaMatrixEmbeddingToLimit

end SuccessorTree.NonPrecompact
