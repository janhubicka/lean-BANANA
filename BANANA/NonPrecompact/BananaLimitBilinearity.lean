import BANANA.NonPrecompact.BananaExplicitLimit
import Mathlib.Data.Finsupp.SMul

/-!
# Scalar bilinearity of the explicit countable BANANA pairing

The basic explicit-limit module already proves additivity in both
coordinates. Here we prove scalar compatibility over F₂. Together these
facts make the parity-of-intersection relation a genuinely bilinear
pairing on the two vector-space sorts.

This is the next algebraic input to showing that the cross-pairing
table of a finite tuple determines pairings of all linear combinations.
-/

namespace SuccessorTree.NonPrecompact

/-- The pairing is compatible with scalar multiplication on the left. -/
theorem bananaLimitPairing_smul_left (c : F2)
    (x y : BananaLimitVector) :
    bananaLimitPairing (c • x) y = c * bananaLimitPairing x y := by
  classical
  calc
    bananaLimitPairing (c • x) y =
        x.sum (fun q a => (c * a) * y q) := by
      unfold bananaLimitPairing
      exact Finsupp.sum_smul_index (g := x) (b := c)
        (h := fun q a => a * y q) (by intro; simp)
    _ = c * bananaLimitPairing x y := by
      change (∑ q ∈ x.support, (c * x q) * y q) =
        c * (∑ q ∈ x.support, x q * y q)
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      ring

/-- The pairing is compatible with scalar multiplication on the right. -/
theorem bananaLimitPairing_smul_right (c : F2)
    (x y : BananaLimitVector) :
    bananaLimitPairing x (c • y) = c * bananaLimitPairing x y := by
  classical
  calc
    bananaLimitPairing x (c • y) =
        ∑ q ∈ x.support, x q * (c * y q) := by
      change (∑ q ∈ x.support, x q * (c • y) q) =
        ∑ q ∈ x.support, x q * (c * y q)
      simp [Finsupp.smul_apply, smul_eq_mul]
    _ = c * bananaLimitPairing x y := by
      change (∑ q ∈ x.support, x q * (c * y q)) =
        c * (∑ q ∈ x.support, x q * y q)
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      ring

/-- The pairing with a fixed right vector is a linear functional. -/
noncomputable def bananaLimitPairingLeftLinear
    (y : BananaLimitVector) : BananaLimitVector →ₗ[F2] F2 where
  toFun := fun x => bananaLimitPairing x y
  map_add' := by
    intro x z
    exact bananaLimitPairing_add_left x z y
  map_smul' := by
    intro c x
    simpa only [smul_eq_mul, RingHom.id_apply] using bananaLimitPairing_smul_left c x y

/-- The pairing with a fixed left vector is a linear functional. -/
noncomputable def bananaLimitPairingRightLinear
    (x : BananaLimitVector) : BananaLimitVector →ₗ[F2] F2 where
  toFun := fun y => bananaLimitPairing x y
  map_add' := by
    intro y z
    exact bananaLimitPairing_add_right x y z
  map_smul' := by
    intro c y
    simpa only [smul_eq_mul, RingHom.id_apply] using bananaLimitPairing_smul_right c x y

end SuccessorTree.NonPrecompact
