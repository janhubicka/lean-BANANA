import BANANA.NonPrecompact.BananaLimitOrthogonality
import Mathlib.LinearAlgebra.Finsupp.Supported

/-!
# Splitting the countable BANANA limit into a finite block and its complement

For a finite rational-coordinate set S, projection to the S-supported
vectors is a linear retraction of the inclusion of the finite block.
Subtracting this projection leaves a vector supported outside S.

These algebraic identities are a prerequisite for extending a finite
block automorphism to the full countable finite-support pairing by
the identity outside S. They do not assert homogeneity yet.
-/

namespace SuccessorTree.NonPrecompact

/-- Linear projection of a finitely supported vector to its
coordinates in S. The codomain is the finite S-supported block. -/
noncomputable def bananaLimitFinitePart (S : Finset ℚ) :
    BananaLimitVector →ₗ[F2] bananaLimitBlock S := by
  classical
  exact Finsupp.restrictDom F2 F2 (S : Set ℚ)

/-- The projection acts pointwise by retaining coordinates in S. -/
theorem bananaLimitFinitePart_apply
    (S : Finset ℚ) (x : BananaLimitVector) (q : ℚ) :
    ((bananaLimitFinitePart S x : bananaLimitBlock S) :
        BananaLimitVector) q =
      if q ∈ S then x q else 0 := by
  classical
  change (Finsupp.filter (· ∈ (S : Set ℚ)) x) q =
    if q ∈ S then x q else 0
  by_cases hq : q ∈ S <;> simp [Finsupp.filter_apply, hq]

/-- Projection is the identity on the included finite block. -/
theorem bananaLimitFinitePart_on_block
    (S : Finset ℚ) (x : bananaLimitBlock S) :
    bananaLimitFinitePart S (x : BananaLimitVector) = x := by
  classical
  change (Finsupp.restrictDom F2 F2 (S : Set ℚ))
      ((bananaLimitBlock S).subtype x) = x
  exact LinearMap.congr_fun
    (Finsupp.restrictDom_comp_subtype (M := F2)
      (R := F2) (s := (S : Set ℚ))) x

/-- Linear projection to the coordinates outside the finite block. -/
noncomputable def bananaLimitOutsidePart (S : Finset ℚ) :
    BananaLimitVector →ₗ[F2] BananaLimitVector :=
  LinearMap.id - (bananaLimitBlock S).subtype.comp
    (bananaLimitFinitePart S)

/-- Each vector is the sum of its inside and outside coordinates. -/
theorem bananaLimit_finite_outside_decomposition
    (S : Finset ℚ) (x : BananaLimitVector) :
    (bananaLimitFinitePart S x : BananaLimitVector) +
      bananaLimitOutsidePart S x = x := by
  change (bananaLimitFinitePart S x : BananaLimitVector) +
      (x - (bananaLimitFinitePart S x : BananaLimitVector)) = x
  abel

/-- The outside projection has no coordinates inside S. -/
theorem bananaLimitFinitePart_outside_zero
    (S : Finset ℚ) (x : BananaLimitVector) :
    bananaLimitFinitePart S (bananaLimitOutsidePart S x) = 0 := by
  change bananaLimitFinitePart S
      (x - (bananaLimitFinitePart S x : BananaLimitVector)) = 0
  rw [map_sub, bananaLimitFinitePart_on_block]
  exact sub_self _

/-- For q in S, the outside part has zero q-coordinate. -/
theorem bananaLimitOutsidePart_apply_mem
    (S : Finset ℚ) (x : BananaLimitVector)
    (q : ℚ) (hq : q ∈ S) :
    (bananaLimitOutsidePart S x) q = 0 := by
  have h := congrArg
    (fun z : bananaLimitBlock S => (z : BananaLimitVector) q)
    (bananaLimitFinitePart_outside_zero S x)
  simpa [bananaLimitFinitePart_apply, hq] using h

/-- The outside part of any vector is pairing-orthogonal to every
vector supported inside S. -/
theorem bananaLimitPairing_outside_block_zero
    (S : Finset ℚ) (x : BananaLimitVector)
    (y : bananaLimitBlock S) :
    bananaLimitPairing (bananaLimitOutsidePart S x)
      (y : BananaLimitVector) = 0 := by
  apply bananaLimitPairing_eq_zero_of_disjoint_support
  apply Finset.disjoint_left.mpr
  intro q hq hy
  have hqS : q ∈ S :=
    ((bananaLimitBlock_mem_iff S (y : BananaLimitVector)).mp
      y.property) hy
  have hz : (bananaLimitOutsidePart S x) q = 0 :=
    bananaLimitOutsidePart_apply_mem S x q hqS
  exact (Finsupp.mem_support_iff.mp hq) hz

end SuccessorTree.NonPrecompact
