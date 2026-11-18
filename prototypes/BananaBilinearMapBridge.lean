import BANANA.NonPrecompact.BananaLimitBilinearity
import Mathlib.LinearAlgebra.BilinearMap

/-!
# Prototype: a mathlib bilinear-map interface for the BANANA limit

**Experimental, not yet kernel-checked.** This module deliberately lives
outside the production `BANANA` import graph until the exact pinned local
Lean toolchain has compiled it and its downstream uses have been reviewed.

The two BANANA vector-space sorts remain independent even though this
particular explicit limit models both of them by the same carrier type.
There is no symmetry or nondegeneracy premise.
-/

namespace SuccessorTree.NonPrecompact

/-- The explicit parity-of-intersection pairing as a genuine bundled
two-variable bilinear map, reusing the existing verified scalar lemmas. -/
noncomputable def bananaLimitPairingBilinear :
    BananaLimitVector →ₗ[F2] BananaLimitVector →ₗ[F2] F2 :=
  LinearMap.mk₂ F2 bananaLimitPairing
    (fun x z y => bananaLimitPairing_add_left x z y)
    (fun c x y => by
      simpa only [smul_eq_mul] using bananaLimitPairing_smul_left c x y)
    (fun x y z => bananaLimitPairing_add_right x y z)
    (fun c x y => by
      simpa only [smul_eq_mul] using bananaLimitPairing_smul_right c x y)

@[simp] theorem bananaLimitPairingBilinear_apply
    (x y : BananaLimitVector) :
    bananaLimitPairingBilinear x y = bananaLimitPairing x y := rfl

/-- Recover the existing left-linear functional by fixing the
right argument of the bundled pairing. -/
theorem bananaLimitPairingBilinear_left_fixed
    (y : BananaLimitVector) :
    (LinearMap.flip bananaLimitPairingBilinear) y =
      bananaLimitPairingLeftLinear y := by
  ext x
  rfl

/-- Recover the existing right-linear functional by fixing the
left argument of the bundled pairing. -/
theorem bananaLimitPairingBilinear_right_fixed
    (x : BananaLimitVector) :
    bananaLimitPairingBilinear x = bananaLimitPairingRightLinear x := by
  ext y
  rfl

/-- The standard bilinear pullback reproduces the pairing on the images
of arbitrary linear maps, with no injectivity assumptions. -/
theorem bananaLimitPairingBilinear_pullback
    {L R : Type*} [AddCommGroup L] [Module F2 L]
    [AddCommGroup R] [Module F2 R]
    (f : L →ₗ[F2] BananaLimitVector)
    (g : R →ₗ[F2] BananaLimitVector)
    (x : L) (y : R) :
    (bananaLimitPairingBilinear.compl₁₂ f g) x y =
      bananaLimitPairing (f x) (g y) := rfl

/-- The standard restriction API preserves the actual pairing on
both subspace carriers. -/
theorem bananaLimitPairingBilinear_restrict
    (U V : Submodule F2 BananaLimitVector)
    (x : U) (y : V) :
    (bananaLimitPairingBilinear.domRestrict₁₂ U V) x y =
      bananaLimitPairing x y := rfl

/-- The original pointwise automorphism equation can be expressed
as one equation of bilinear maps. -/
theorem bananaLimitPairingBilinear_invariant
    (f g : BananaLimitVector ≃ₗ[F2] BananaLimitVector)
    (h : ∀ x y, bananaLimitPairing (f x) (g y) =
      bananaLimitPairing x y) :
    bananaLimitPairingBilinear.compl₁₂ f.toLinearMap g.toLinearMap =
      bananaLimitPairingBilinear := by
  apply LinearMap.ext₂
  intro x y
  change bananaLimitPairing (f x) (g y) = bananaLimitPairing x y
  exact h x y

end SuccessorTree.NonPrecompact

#print axioms SuccessorTree.NonPrecompact.bananaLimitPairingBilinear
#print axioms SuccessorTree.NonPrecompact.bananaLimitPairingBilinear_invariant
