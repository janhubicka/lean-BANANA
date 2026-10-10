import BANANA.NonPrecompact.BananaLimitFiniteGLApproximation
import BANANA.NonPrecompact.BananaLimitFiniteAge
import BANANA.NonPrecompact.BananaLimitLocalFiniteness

/-!
# Pointwise approximation by finite coordinate automorphisms

Given an arbitrary pairing-preserving pair of linear automorphisms of
the countable BANANA limit and two finite sets of test vectors, we
construct a perfect-coordinate block and its finite general-linear
action agreeing with the prescribed automorphisms on all test vectors.

This is the algebraic finite-neighbourhood criterion for density of
the union of the finite coordinate-block automorphism groups in the
pointwise convergence topology. The topological density statement and
the amenability implication are not asserted in this module.
-/

namespace SuccessorTree.NonPrecompact

/-- Every global pairing automorphism admits a finite-coordinate GL
approximant agreeing with it on any prescribed finite families on both
sorts. The action is the standard contragredient pair extended by the
identity outside one finite rational-coordinate block. -/
theorem exists_finiteGLAction_agree_on_finite_sets
    (gL gR : BananaLimitVector ≃ₗ[F2] BananaLimitVector)
    (hpair : ∀ x y : BananaLimitVector,
      bananaLimitPairing (gL x) (gR y) =
        bananaLimitPairing x y)
    (left right : Finset BananaLimitVector) :
    ∃ S : Finset ℚ, ∃ h : FinitePerfectGL S.card,
      (∀ x ∈ left,
        (bananaLimitFiniteGLAction S h).1 x = gL x) ∧
      (∀ y ∈ right,
        (bananaLimitFiniteGLAction S h).2 y = gR y) := by
  classical
  let U : Submodule F2 BananaLimitVector :=
    Submodule.span F2 (left : Set BananaLimitVector)
  let V : Submodule F2 BananaLimitVector :=
    Submodule.span F2 (right : Set BananaLimitVector)
  letI : Finite U := bananaLimit_finitely_generated_span_finite left
  letI : Finite V := bananaLimit_finitely_generated_span_finite right
  obtain ⟨l, r, A, e₁, hrangeL, hrangeR⟩ :=
    exists_finite_banana_substructure_of_limit U V
  let e₂ : BananaMatrixEmbeddingToLimit A := {
    left := gL.toLinearMap.comp e₁.left
    right := gR.toLinearMap.comp e₁.right
    left_injective := gL.injective.comp e₁.left_injective
    right_injective := gR.injective.comp e₁.right_injective
    pairing_apply := by
      intro x y
      change bananaLimitPairing (gL (e₁.left x))
        (gR (e₁.right y)) = A.eval x y
      exact (hpair (e₁.left x) (e₁.right y)).trans
        (e₁.pairing_apply x y)
  }
  obtain ⟨S, h, hleft, hright⟩ :=
    e₁.exists_finiteGLAction_matching_embeddings e₂
  refine ⟨S, h, ?_, ?_⟩
  · intro x hx
    have hxU : x ∈ U := Submodule.subset_span hx
    have hxRange : x ∈ LinearMap.range e₁.left := by
      rw [hrangeL]
      exact hxU
    obtain ⟨a, ha⟩ := hxRange
    calc
      (bananaLimitFiniteGLAction S h).1 x =
          (bananaLimitFiniteGLAction S h).1 (e₁.left a) := by
            rw [ha]
      _ = e₂.left a := hleft a
      _ = gL x := by
        change gL (e₁.left a) = gL x
        rw [ha]
  · intro y hy
    have hyV : y ∈ V := Submodule.subset_span hy
    have hyRange : y ∈ LinearMap.range e₁.right := by
      rw [hrangeR]
      exact hyV
    obtain ⟨b, hb⟩ := hyRange
    calc
      (bananaLimitFiniteGLAction S h).2 y =
          (bananaLimitFiniteGLAction S h).2 (e₁.right b) := by
            rw [hb]
      _ = e₂.right b := hright b
      _ = gR y := by
        change gR (e₁.right b) = gR y
        rw [hb]

end SuccessorTree.NonPrecompact
