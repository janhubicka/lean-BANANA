import BANANA.NonPrecompact.BananaLimitBlockLiftGroupLaw
import BANANA.NonPrecompact.BananaLimitBlockProjection

/-!
# Nested finite supports for automorphisms of the BANANA limit

A finite-block automorphism supported on S preserves every finite
coordinate block indexed by a superset T of S. The same holds for its
outside-coordinate component, because it is a difference of vectors
already supported inside T.

These are the support-invariance ingredients for identifying the
finite GL subgroup at S with a subgroup of the stage at T. The actual
parameter transport GL(S) → GL(T) is a subsequent lemma.
-/

namespace SuccessorTree.NonPrecompact

/-- The S-coordinate projection lies in every larger T-block. -/
theorem bananaLimitFinitePart_mem_larger_block
    (S T : Finset ℚ) (hST : S ⊆ T)
    (x : BananaLimitVector) :
    (bananaLimitFinitePart S x : BananaLimitVector) ∈
      bananaLimitBlock T :=
  (bananaLimitBlock_mono hST)
    (bananaLimitFinitePart S x).property

/-- The component outside S remains in T if the original vector lies
inside T and S is a subset of T. -/
theorem bananaLimitOutsidePart_mem_larger_block
    (S T : Finset ℚ) (hST : S ⊆ T)
    (x : BananaLimitVector) (hx : x ∈ bananaLimitBlock T) :
    bananaLimitOutsidePart S x ∈ bananaLimitBlock T := by
  change x - (bananaLimitFinitePart S x : BananaLimitVector) ∈
    bananaLimitBlock T
  exact (bananaLimitBlock T).sub_mem hx
    (bananaLimitFinitePart_mem_larger_block S T hST x)

/-- Every globally lifted automorphism of a finite S-supported block
preserves membership of each larger finite T-supported block. -/
theorem bananaLimitBlockLift_mem_larger_block
    (S T : Finset ℚ) (hST : S ⊆ T)
    (e : bananaLimitBlock S ≃ₗ[F2] bananaLimitBlock S)
    (x : BananaLimitVector) (hx : x ∈ bananaLimitBlock T) :
    bananaLimitBlockLift S e x ∈ bananaLimitBlock T := by
  rw [bananaLimitBlockLift_apply]
  exact (bananaLimitBlock T).add_mem
    ((bananaLimitBlock_mono hST)
      (e (bananaLimitFinitePart S x)).property)
    (bananaLimitOutsidePart_mem_larger_block S T hST x hx)

end SuccessorTree.NonPrecompact
