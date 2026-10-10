import BANANA.NonPrecompact.BananaLimitBlockSupportMonotonicity
import BANANA.NonPrecompact.BananaLimitBlockLiftGroupLaw

/-!
# Restricting a finite-block BANANA automorphism to a larger block

When S⊆T are finite rational-coordinate sets, a globally lifted
automorphism of the S-supported block preserves the larger T-block.
The restriction is a genuine linear equivalence on T; its inverse is
the restriction of the inverse S-block transformation.

This supplies the intrinsic finite-block extension mechanism needed
for the inclusions of finite subgroup stages indexed by finite
rational supports. Choosing compatible standard-coordinate matrices
on those stages is a separate construction.
-/

namespace SuccessorTree.NonPrecompact

/-- The inverse of a block lift is exactly the lift of the inverse
finite-block transformation. -/
theorem bananaLimitBlockLift_symm
    (S : Finset ℚ)
    (e : bananaLimitBlock S ≃ₗ[F2] bananaLimitBlock S) :
    (bananaLimitBlockLift S e).symm =
      bananaLimitBlockLift S e.symm := by
  apply LinearEquiv.ext
  intro x
  rfl

/-- Restrict a smaller-block transformation to a larger finite block.
Its inverse is obtained by restricting the lifted inverse. -/
noncomputable def bananaLimitBlockLiftRestrict
    (S T : Finset ℚ) (hST : S ⊆ T)
    (e : bananaLimitBlock S ≃ₗ[F2] bananaLimitBlock S) :
    bananaLimitBlock T ≃ₗ[F2] bananaLimitBlock T where
  toFun x :=
    ⟨bananaLimitBlockLift S e x,
      bananaLimitBlockLift_mem_larger_block S T hST e x x.property⟩
  invFun x :=
    ⟨bananaLimitBlockLift S e.symm x,
      bananaLimitBlockLift_mem_larger_block S T hST e.symm x x.property⟩
  left_inv := by
    intro x
    apply Subtype.ext
    change bananaLimitBlockLift S e.symm
      (bananaLimitBlockLift S e (x : BananaLimitVector)) =
        (x : BananaLimitVector)
    rw [← bananaLimitBlockLift_symm]
    exact (bananaLimitBlockLift S e).symm_apply_apply _
  right_inv := by
    intro x
    apply Subtype.ext
    change bananaLimitBlockLift S e
      (bananaLimitBlockLift S e.symm (x : BananaLimitVector)) =
        (x : BananaLimitVector)
    rw [← bananaLimitBlockLift_symm]
    exact (bananaLimitBlockLift S e).apply_symm_apply _
  map_add' := by
    intro x y
    apply Subtype.ext
    change bananaLimitBlockLift S e
      ((x : BananaLimitVector) + (y : BananaLimitVector)) =
        bananaLimitBlockLift S e x + bananaLimitBlockLift S e y
    exact (bananaLimitBlockLift S e).map_add x y
  map_smul' := by
    intro a x
    apply Subtype.ext
    change bananaLimitBlockLift S e
      (a • (x : BananaLimitVector)) =
        a • bananaLimitBlockLift S e x
    exact (bananaLimitBlockLift S e).map_smul a x

/-- On the underlying ambient vector, restriction of a block lift
has exactly the same action as the original global lift. -/
theorem bananaLimitBlockLiftRestrict_apply
    (S T : Finset ℚ) (hST : S ⊆ T)
    (e : bananaLimitBlock S ≃ₗ[F2] bananaLimitBlock S)
    (x : bananaLimitBlock T) :
    (bananaLimitBlockLiftRestrict S T hST e x :
      BananaLimitVector) =
      bananaLimitBlockLift S e (x : BananaLimitVector) := rfl

/-- Pairing-preserving transformations supported on S remain
pairing-preserving after restriction to any larger finite T-block. -/
theorem bananaLimitBlockLiftRestrict_pairing
    (S T : Finset ℚ) (hST : S ⊆ T)
    (eL eR : bananaLimitBlock S ≃ₗ[F2] bananaLimitBlock S)
    (hpair : ∀ u v : bananaLimitBlock S,
      bananaLimitPairing (eL u : BananaLimitVector)
        (eR v : BananaLimitVector) =
        bananaLimitPairing (u : BananaLimitVector)
          (v : BananaLimitVector))
    (x y : bananaLimitBlock T) :
    bananaLimitPairing
      (bananaLimitBlockLiftRestrict S T hST eL x :
        BananaLimitVector)
      (bananaLimitBlockLiftRestrict S T hST eR y :
        BananaLimitVector) =
      bananaLimitPairing (x : BananaLimitVector)
        (y : BananaLimitVector) := by
  change bananaLimitPairing
    (bananaLimitBlockLift S eL (x : BananaLimitVector))
    (bananaLimitBlockLift S eR (y : BananaLimitVector)) =
      bananaLimitPairing (x : BananaLimitVector)
        (y : BananaLimitVector)
  exact bananaLimitBlockLift_pairing S eL eR hpair x y

end SuccessorTree.NonPrecompact
