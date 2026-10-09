import BANANA.NonPrecompact.BananaFiniteSupportBlocks

/-!
# Orthogonality of disjoint coordinate supports in the BANANA limit

The intersection-parity pairing vanishes when its two arguments
have disjoint supports. In particular, two finite supported blocks
are mutually orthogonal if their coordinate sets are disjoint.

This lemma is the finite-support geometric input to extending a
perfect-block automorphism by the identity on all coordinates
outside that block. It is deliberately separated from the later
global automorphism extension theorem.
-/

namespace SuccessorTree.NonPrecompact

/-- Vectors with disjoint finite coordinate supports are orthogonal
for the parity-of-intersection bilinear pairing. -/
theorem bananaLimitPairing_eq_zero_of_disjoint_support
    (x y : BananaLimitVector)
    (h : Disjoint x.support y.support) :
    bananaLimitPairing x y = 0 := by
  classical
  change (∑ q ∈ x.support, x q * y q) = 0
  apply Finset.sum_eq_zero
  intro q hq
  have hnot : q ∉ y.support := by
    intro hy
    exact (Finset.disjoint_left.mp h) hq hy
  simp [Finsupp.notMem_support_iff.mp hnot]

/-- Pairings between distinct disjoint finite-coordinate blocks
vanish in both left/right orientations. -/
theorem bananaLimitPairing_eq_zero_of_disjoint_blocks
    (S T : Finset ℚ) (hST : Disjoint S T)
    (x : bananaLimitBlock S) (y : bananaLimitBlock T) :
    bananaLimitPairing x y = 0 := by
  apply bananaLimitPairing_eq_zero_of_disjoint_support
  apply Finset.disjoint_left.mpr
  intro q hqx hqy
  have hS : q ∈ S :=
    ((bananaLimitBlock_mem_iff S (x : BananaLimitVector)).1 x.property) hqx
  have hT : q ∈ T :=
    ((bananaLimitBlock_mem_iff T (y : BananaLimitVector)).1 y.property) hqy
  exact (Finset.disjoint_left.mp hST) hS hT

end SuccessorTree.NonPrecompact
