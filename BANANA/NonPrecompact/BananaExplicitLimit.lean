import BANANA.NonPrecompact.BananaFiniteCountability
import Mathlib.LinearAlgebra.Finsupp.Pi

/-!
# The explicit countable BANANA pairing

This is the concrete model appearing in the circulation manuscript:
on each sort take the finite subsets of the rational numbers, written
equivalently as finitely supported F₂-valued functions on ℚ.
The pairing is the parity of the intersection of their supports.

We begin with a representation and the elementary finite-support
and bilinearity lemmas. Embedding every finite BANANA structure,
homogeneity of this infinite model and ω-categoricity remain
separate Lean obligations.

This module does not change the frozen circulation text.
-/

namespace SuccessorTree.NonPrecompact

/-- A finite binary subset of ℚ, represented as a coordinate vector
with finite support. -/
abbrev BananaLimitVector := ℚ →₀ F2

/-- Dot product of two finitely supported binary coordinate vectors.
It counts the intersection of their supports modulo two. -/
def bananaLimitPairing (x y : BananaLimitVector) : F2 :=
  x.sum (fun q a => a * y q)

/-- The E-relation in the explicitly constructed limit. -/
def bananaLimitEdge (x y : BananaLimitVector) : Prop :=
  bananaLimitPairing x y = 1

/-- The finite-support vector space is countable: ℚ and F₂ are
countable, and every vector has only finitely many coordinates. -/
instance bananaLimitVectorCountable : Countable BananaLimitVector :=
  inferInstance

theorem bananaLimitPairing_zero_left (y : BananaLimitVector) :
    bananaLimitPairing 0 y = 0 := by
  simp [bananaLimitPairing]

theorem bananaLimitPairing_zero_right (x : BananaLimitVector) :
    bananaLimitPairing x 0 = 0 := by
  classical
  simp [bananaLimitPairing]

/-- Linearity of the pairing in the first coordinate. -/
theorem bananaLimitPairing_add_left
    (x z y : BananaLimitVector) :
    bananaLimitPairing (x + z) y =
      bananaLimitPairing x y + bananaLimitPairing z y := by
  classical
  unfold bananaLimitPairing
  exact Finsupp.sum_add_index (by simp) (by simp [add_mul])

/-- Linearity of the pairing in the second coordinate. -/
theorem bananaLimitPairing_add_right
    (x y z : BananaLimitVector) :
    bananaLimitPairing x (y + z) =
      bananaLimitPairing x y + bananaLimitPairing x z := by
  classical
  simp [bananaLimitPairing, Finsupp.sum, mul_add,
    Finset.sum_add_distrib]

/-- The coordinate basis of the explicit limit has Kronecker
pairing: different coordinates are orthogonal, and each basis
vector pairs to one with itself. -/
theorem bananaLimitPairing_single
    (p q : ℚ) :
    bananaLimitPairing (Finsupp.single p 1) (Finsupp.single q 1) =
      if p = q then 1 else 0 := by
  classical
  by_cases h : p = q
  · subst q
    simp [bananaLimitPairing]
  · simp [bananaLimitPairing, h, Finsupp.single_apply]

/-- The common finite coordinate support of two finite families of
vectors. Every vector appearing in either family is supported here. -/
def bananaLimitCommonSupport
    (left right : Finset BananaLimitVector) : Finset ℚ :=
  (left.biUnion (fun x => x.support)) ∪
    (right.biUnion (fun y => y.support))

theorem bananaLimit_left_support_subset
    (left right : Finset BananaLimitVector)
    (x : BananaLimitVector) (hx : x ∈ left) :
    x.support ⊆ bananaLimitCommonSupport left right := by
  intro q hq
  exact Finset.mem_union_left _
    (Finset.mem_biUnion.mpr ⟨x, hx, hq⟩)

theorem bananaLimit_right_support_subset
    (left right : Finset BananaLimitVector)
    (y : BananaLimitVector) (hy : y ∈ right) :
    y.support ⊆ bananaLimitCommonSupport left right := by
  intro q hq
  exact Finset.mem_union_right _
    (Finset.mem_biUnion.mpr ⟨y, hy, hq⟩)

end SuccessorTree.NonPrecompact
