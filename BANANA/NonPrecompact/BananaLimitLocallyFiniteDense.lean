import BANANA.NonPrecompact.BananaLimitDirectedGLUnion
import BANANA.NonPrecompact.BananaLimitFiniteGLDensity

/-!
# The locally finite dense subgroup: algebraic neighbourhood criterion

The directed union of finite perfect-block GL stages is locally finite.
The previously verified finite-pointwise approximation theorem shows
that for every pairing automorphism and finite test families, a member
of this *same union* agrees on all specified vectors.

This is the concrete finite-neighbourhood criterion for density in the
pointwise convergence topology on the two-sorted automorphism group.
The standard abstract topological implication and the subsequent
amenability theorem are cited separately rather than imported as Lean
axioms.
-/

namespace SuccessorTree.NonPrecompact

/-- Members of the directed finite-stage union approximate any
pairing-preserving two-sorted global automorphism on prescribed
finite families, on both sides simultaneously. -/
theorem bananaLimitFiniteGLUnion_pointwise_approximates
    (gL gR : BananaLimitVector ≃ₗ[F2] BananaLimitVector)
    (hpair : ∀ x y : BananaLimitVector,
      bananaLimitPairing (gL x) (gR y) =
        bananaLimitPairing x y)
    (left right : Finset BananaLimitVector) :
    ∃ f : BananaLimitLinearPair,
      f ∈ bananaLimitFiniteGLUnion ∧
      (∀ x ∈ left, f.1 x = gL x) ∧
      (∀ y ∈ right, f.2 y = gR y) := by
  obtain ⟨S, h, hL, hR⟩ :=
    exists_finiteGLAction_agree_on_finite_sets
      gL gR hpair left right
  exact ⟨bananaLimitFiniteGLAction S h,
    ⟨S, ⟨h, rfl⟩⟩, hL, hR⟩

end SuccessorTree.NonPrecompact
