import BANANA.NonPrecompact.BananaFiniteSupportBlocks
import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Perfect pairing on every finite coordinate block of the BANANA limit

A finite set S of rational coordinates determines the subspace of
binary finitely supported vectors whose support lies in S.
Restriction to S is a linear equivalence to the standard finite
function space S → F₂.

The ambient intersection-parity pairing restricts exactly to the
usual dot product on that finite coordinate space. In particular,
the chosen coordinate functions give dual bases and the block
is a perfect pairing. This is the structural input to extending
finite partial automorphisms inside a suitable finite block.
-/

namespace SuccessorTree.NonPrecompact

open Module

/-- Restriction to the finite set S is just evaluation at a
coordinate belonging to S. -/
@[simp] theorem bananaLimitBlockEquiv_apply
    (S : Finset ℚ)
    (x : bananaLimitBlock S)
    (q : {q : ℚ // q ∈ S}) :
    bananaLimitBlockEquiv S x q = (x : BananaLimitVector) q := by
  rfl

/-- The ambient bilinear pairing restricted to a finite block agrees
with the ordinary dot product of its finite coordinate vectors. -/
theorem bananaLimitBlock_pairing_eq_dotProduct
    (S : Finset ℚ) (x y : bananaLimitBlock S) :
    bananaLimitPairing x y =
      (bananaLimitBlockEquiv S x) ⬝ᵥ
      (bananaLimitBlockEquiv S y) := by
  classical
  calc
    bananaLimitPairing x y =
        ∑ q ∈ S, (x : BananaLimitVector) q *
          (y : BananaLimitVector) q :=
      bananaLimitPairing_eq_sum_of_mem_block S x y x.property
    _ = ∑ q : {q : ℚ // q ∈ S},
          (x : BananaLimitVector) q * (y : BananaLimitVector) q := by
      exact (Finset.sum_coe_sort S
        (fun q => (x : BananaLimitVector) q * (y : BananaLimitVector) q)).symm
    _ = (bananaLimitBlockEquiv S x) ⬝ᵥ
          (bananaLimitBlockEquiv S y) := by
      simp [dotProduct, bananaLimitBlockEquiv_apply]

/-- The finite-coordinate equivalence gives a concrete basis of
the S-supported subspace, without any global choice of bases. -/
noncomputable def bananaLimitBlockBasis (S : Finset ℚ) :
    Basis {q : ℚ // q ∈ S} F2 (bananaLimitBlock S) :=
  Basis.ofEquivFun (bananaLimitBlockEquiv S)

/-- Every finite block is paired perfectly with itself. Expressed
using the equivalence to finite functions, this is the usual
non-degenerate standard dot product. -/
theorem bananaLimitBlock_basis_pairing
    (S : Finset ℚ)
    (p q : {q : ℚ // q ∈ S}) :
    bananaLimitPairing
      (bananaLimitBlockBasis S p)
      (bananaLimitBlockBasis S q) =
    if p = q then 1 else 0 := by
  classical
  have hcoords (i : {q : ℚ // q ∈ S}) :
      bananaLimitBlockEquiv S (bananaLimitBlockBasis S i) =
        Pi.single i (1 : F2) := by
    simp [bananaLimitBlockBasis, Basis.coe_ofEquivFun]
  rw [bananaLimitBlock_pairing_eq_dotProduct, hcoords p, hcoords q]
  simp [Pi.single_apply, eq_comm]

end SuccessorTree.NonPrecompact
