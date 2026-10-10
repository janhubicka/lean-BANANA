import BANANA.NonPrecompact.BananaLimitBlockRestriction
import BANANA.NonPrecompact.BananaLimitOutsideLargerBlock

/-!
# A finite-block lift is the global lift of its larger-block restriction

Suppose S⊆T. The automorphism of the countable BANANA pairing
supported on S preserves the T-supported block. Restricting to T
and extending that restriction by the identity outside T gives
the original global automorphism.

This is the key compatibility identity for directed finite GL
subgroup stages indexed by arbitrary finite rational supports.
-/

namespace SuccessorTree.NonPrecompact

/-- Lifting the restriction of a finite S-block automorphism to a
larger T-block gives precisely the original global S-block lift. -/
theorem bananaLimitBlockLift_extend_restriction
    (S T : Finset ℚ) (hST : S ⊆ T)
    (e : bananaLimitBlock S ≃ₗ[F2] bananaLimitBlock S) :
    bananaLimitBlockLift T
      (bananaLimitBlockLiftRestrict S T hST e) =
    bananaLimitBlockLift S e := by
  apply LinearEquiv.ext
  intro x
  calc
    bananaLimitBlockLift T
        (bananaLimitBlockLiftRestrict S T hST e) x =
      (bananaLimitBlockLiftRestrict S T hST e
          (bananaLimitFinitePart T x) : BananaLimitVector) +
        bananaLimitOutsidePart T x := by
          rw [bananaLimitBlockLift_apply]
    _ = bananaLimitBlockLift S e
          (bananaLimitFinitePart T x : BananaLimitVector) +
        bananaLimitOutsidePart T x := by
          rw [bananaLimitBlockLiftRestrict_apply]
    _ = bananaLimitBlockLift S e
          ((bananaLimitFinitePart T x : BananaLimitVector) +
            bananaLimitOutsidePart T x) := by
          rw [map_add,
            bananaLimitBlockLift_fixed_outside_larger_block S T hST e x]
    _ = bananaLimitBlockLift S e x := by
          rw [bananaLimit_finite_outside_decomposition T x]

end SuccessorTree.NonPrecompact
