import BANANA.NonPrecompact.BananaLimitFiniteGLAction
import BANANA.NonPrecompact.BananaLimitFinitePairHomogeneity
import BANANA.NonPrecompact.PerfectSelfEmbedding

/-!
# Finite GL actions matching any two embedded finite BANANA structures

Finite-dimensional perfect-pair homogeneity can be applied inside one
coordinate block containing two given embeddings. The resulting block
automorphism is necessarily determined by a left GL transformation and
its right contragredient. The associated finite-block action on the
entire countable limit matches the two embeddings pointwise.

This is the finite approximation property for a prescribed embedded
finite structure, before passing to arbitrary finite test families and
the pointwise convergence topology.
-/

namespace SuccessorTree.NonPrecompact

namespace BananaMatrixEmbeddingToLimit

/-- Every two embeddings of the same finite BANANA pairing into the
countable limit can be matched by an automorphism supported inside
one finite rational-coordinate block and parametrised by its GL group. -/
theorem exists_finiteGLAction_matching_embeddings
    {l r : ℕ} {A : BananaMatrixStructure l r}
    (e₁ e₂ : BananaMatrixEmbeddingToLimit A) :
    ∃ S : Finset ℚ, ∃ h : FinitePerfectGL S.card,
      (∀ x, (bananaLimitFiniteGLAction S h).1 (e₁.left x) =
        e₂.left x) ∧
      (∀ y, (bananaLimitFiniteGLAction S h).2 (e₁.right y) =
        e₂.right y) := by
  classical
  obtain ⟨S, f₁, f₂, H, h₁L, h₁R, h₂L, h₂R, hL, hR⟩ :=
    e₁.exists_finite_perfect_ambient_automorphism e₂
  let E := bananaLimitBlockStandardEquiv S
  let h : FinitePerfectGL S.card := H.leftSelfEquiv
  refine ⟨S, h, ?_, ?_⟩
  · intro x
    have hh : h (f₁.left x) = f₂.left x := by
      change H.left (f₁.left x) = f₂.left x
      exact hL x
    calc
      (bananaLimitFiniteGLAction S h).1 (e₁.left x) =
          (bananaLimitFiniteGLAction S h).1
            (E (f₁.left x) : BananaLimitVector) := by
          simpa [bananaLimitBlockStandardEmbedding, E] using
            congrArg (bananaLimitFiniteGLAction S h).1 (h₁L x).symm
      _ = (E (h (f₁.left x)) : BananaLimitVector) :=
        bananaLimitFiniteGLAction_left_on_block S h (f₁.left x)
      _ = (E (f₂.left x) : BananaLimitVector) := by rw [hh]
      _ = e₂.left x := by
        simpa [bananaLimitBlockStandardEmbedding, E] using h₂L x
  · intro y
    have hh : dotContragredient h (f₁.right y) = f₂.right y := by
      have hr := hR y
      rw [H.right_eq_dotContragredient_leftSelfEquiv] at hr
      exact hr
    calc
      (bananaLimitFiniteGLAction S h).2 (e₁.right y) =
          (bananaLimitFiniteGLAction S h).2
            (E (f₁.right y) : BananaLimitVector) := by
          simpa [bananaLimitBlockStandardEmbedding, E] using
            congrArg (bananaLimitFiniteGLAction S h).2 (h₁R y).symm
      _ = (E (dotContragredient h (f₁.right y)) : BananaLimitVector) :=
        bananaLimitFiniteGLAction_right_on_block S h (f₁.right y)
      _ = (E (f₂.right y) : BananaLimitVector) := by rw [hh]
      _ = e₂.right y := by
        simpa [bananaLimitBlockStandardEmbedding, E] using h₂R y

end BananaMatrixEmbeddingToLimit

end SuccessorTree.NonPrecompact
