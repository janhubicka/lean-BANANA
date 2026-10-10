import BANANA.NonPrecompact.BananaLimitBlockPairLift
import BANANA.NonPrecompact.BananaLimitBlockProjection

/-!
# Finite-block lifts fix the outside of every larger coordinate block

If S is contained in T, then projecting a vector supported outside T
onto S gives zero. Thus any finite automorphism supported in S fixes
pointwise the component outside T, not only the component outside S.

This is the complementary ingredient to invariance of larger blocks;
together they allow identification of the global S-block lift with a
lift of its restriction to T.
-/

namespace SuccessorTree.NonPrecompact

/-- No S-coordinate survives in the component outside a larger T. -/
theorem bananaLimitFinitePart_outside_zero_of_subset
    (S T : Finset ℚ) (hST : S ⊆ T)
    (x : BananaLimitVector) :
    bananaLimitFinitePart S (bananaLimitOutsidePart T x) = 0 := by
  classical
  apply Subtype.ext
  ext q
  rw [bananaLimitFinitePart_apply]
  by_cases hq : q ∈ S
  · simp only [if_pos hq]
    exact bananaLimitOutsidePart_apply_mem T x q (hST hq)
  · simp [hq]

/-- A lifted finite-block automorphism fixes any vector whose finite
S-coordinate projection is zero. -/
theorem bananaLimitBlockLift_fixed_of_projection_zero
    (S : Finset ℚ)
    (e : bananaLimitBlock S ≃ₗ[F2] bananaLimitBlock S)
    (x : BananaLimitVector)
    (hx : bananaLimitFinitePart S x = 0) :
    bananaLimitBlockLift S e x = x := by
  rw [bananaLimitBlockLift_apply, hx]
  have hout := bananaLimit_finite_outside_decomposition S x
  rw [hx] at hout
  simpa using hout

/-- Every S-supported automorphism fixes the entire outside component
of a T-block when S⊆T. -/
theorem bananaLimitBlockLift_fixed_outside_larger_block
    (S T : Finset ℚ) (hST : S ⊆ T)
    (e : bananaLimitBlock S ≃ₗ[F2] bananaLimitBlock S)
    (x : BananaLimitVector) :
    bananaLimitBlockLift S e (bananaLimitOutsidePart T x) =
      bananaLimitOutsidePart T x :=
  bananaLimitBlockLift_fixed_of_projection_zero S e _
    (bananaLimitFinitePart_outside_zero_of_subset S T hST x)

end SuccessorTree.NonPrecompact
