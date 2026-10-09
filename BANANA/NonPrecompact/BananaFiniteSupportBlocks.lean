import BANANA.NonPrecompact.BananaExplicitLimit
import Mathlib.LinearAlgebra.Finsupp.Supported

/-!
# Finite perfect-coordinate blocks inside the explicit BANANA limit

The two sorts of the explicit countable BANANA limit are the vector
space of finitely supported binary functions on ℚ. For each finite set
S of rational coordinates, the vectors supported on S form a finite
dimensional subspace. Via restriction to S, this is the standard
finite binary coordinate space indexed by S.

The pairing of vectors in such a block is the ordinary finite dot
product. Every finite family of vectors from both sorts is contained
in one common block. This is the finite-support reduction used in
the circulation proof of ultrahomogeneity.

This module does not yet assert homogeneity, universality, or
ω-categoricity for the countable structure.
-/

namespace SuccessorTree.NonPrecompact

/-- The subspace consisting of the finitely supported binary vectors
whose support is contained in the finite rational set S. -/
def bananaLimitBlock (S : Finset ℚ) : Submodule F2 BananaLimitVector :=
  Finsupp.supported F2 F2 (S : Set ℚ)

/-- Membership of a finite block is exactly the support condition. -/
theorem bananaLimitBlock_mem_iff (S : Finset ℚ)
    (x : BananaLimitVector) :
    x ∈ bananaLimitBlock S ↔ x.support ⊆ S := by
  change (x.support : Set ℚ) ⊆ (S : Set ℚ) ↔ x.support ⊆ S
  exact Finset.coe_subset

/-- Restrict a finite-block vector to its coordinate function
on the finite subtype S. -/
noncomputable def bananaLimitBlockEquiv (S : Finset ℚ) :
    bananaLimitBlock S ≃ₗ[F2] ({q : ℚ // q ∈ S} → F2) :=
  (Finsupp.supportedEquivFinsupp (R := F2) (S : Set ℚ)).trans
    (Finsupp.linearEquivFunOnFinite F2 F2 {q : ℚ // q ∈ S})

/-- Every finite block has finitely many vectors. -/
noncomputable instance bananaLimitBlockFintype (S : Finset ℚ) :
    Fintype (bananaLimitBlock S) := by
  classical
  exact Fintype.ofInjective (bananaLimitBlockEquiv S)
    (bananaLimitBlockEquiv S).injective

/-- Inclusion of finite coordinate sets induces inclusion of blocks. -/
theorem bananaLimitBlock_mono {S T : Finset ℚ} (hST : S ⊆ T) :
    bananaLimitBlock S ≤ bananaLimitBlock T := by
  intro x hx
  exact (bananaLimitBlock_mem_iff T x).2
    (((bananaLimitBlock_mem_iff S x).1 hx).trans hST)

/-- Every finite set of left-sort vectors lies in the common block
obtained by collecting all left and right supports. -/
theorem bananaLimit_left_mem_common_block
    (left right : Finset BananaLimitVector)
    (x : BananaLimitVector) (hx : x ∈ left) :
    x ∈ bananaLimitBlock (bananaLimitCommonSupport left right) :=
  (bananaLimitBlock_mem_iff _ _).2
    (bananaLimit_left_support_subset left right x hx)

/-- Symmetrically every vector of the finite right-sort family
lies in the same common coordinate block. -/
theorem bananaLimit_right_mem_common_block
    (left right : Finset BananaLimitVector)
    (y : BananaLimitVector) (hy : y ∈ right) :
    y ∈ bananaLimitBlock (bananaLimitCommonSupport left right) :=
  (bananaLimitBlock_mem_iff _ _).2
    (bananaLimit_right_support_subset left right y hy)

/-- A finitely supported vector with support in S has its pairing
computed by summing over S, not merely over its own support. -/
theorem bananaLimitPairing_eq_sum_of_mem_block
    (S : Finset ℚ) (x y : BananaLimitVector)
    (hx : x ∈ bananaLimitBlock S) :
    bananaLimitPairing x y = ∑ q ∈ S, x q * y q := by
  classical
  have hsub : x.support ⊆ S :=
    (bananaLimitBlock_mem_iff S x).mp hx
  change (∑ q ∈ x.support, x q * y q) =
    ∑ q ∈ S, x q * y q
  apply Finset.sum_subset hsub
  intro q hq hnot
  simp [Finsupp.notMem_support_iff.mp hnot]

end SuccessorTree.NonPrecompact
