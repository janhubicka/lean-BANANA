import BANANA.NonPrecompact.BananaStructure

/-!
# Lifting automorphisms through linear retractions

Let i : U → V have a linear left inverse p : V → U. Any linear
automorphism e of U extends to a linear automorphism of V by
  x ↦ x + i(e(p x) - p x).
The inverse is obtained by replacing e with e⁻¹.

This construction acts as e on i(U) and as the identity on ker p.
It is independent of finite support or the ambient pairing.
Later we will use the projection to an S-supported rational block
to lift its pairing-preserving automorphisms to the countable limit.
-/

namespace SuccessorTree.NonPrecompact

variable {U V : Type*}
variable [AddCommGroup U] [AddCommGroup V]
variable [Module F2 U] [Module F2 V]

/-- Extend a linear endomorphism of a retract along a chosen
inclusion/retraction pair. No left-inverse hypothesis is needed
for the definition. -/
def bananaRetractionLiftLinear
    (i : U →ₗ[F2] V) (p : V →ₗ[F2] U)
    (e : U →ₗ[F2] U) : V →ₗ[F2] V :=
  LinearMap.id + (i.comp (e - LinearMap.id)).comp p

theorem bananaRetractionLiftLinear_apply
    (i : U →ₗ[F2] V) (p : V →ₗ[F2] U)
    (e : U →ₗ[F2] U) (x : V) :
    bananaRetractionLiftLinear i p e x =
      x + i (e (p x) - p x) := by
  rfl

/-- The projection of a lifted vector is the transformed old
projection when p is a left inverse of i. -/
theorem bananaRetractionLiftLinear_project
    (i : U →ₗ[F2] V) (p : V →ₗ[F2] U)
    (h : ∀ u, p (i u) = u)
    (e : U →ₗ[F2] U) (x : V) :
    p (bananaRetractionLiftLinear i p e x) = e (p x) := by
  rw [bananaRetractionLiftLinear_apply, p.map_add, h]
  abel

/-- A lifted map agrees with e on the embedded subspace. -/
theorem bananaRetractionLiftLinear_on_range
    (i : U →ₗ[F2] V) (p : V →ₗ[F2] U)
    (h : ∀ u, p (i u) = u)
    (e : U →ₗ[F2] U) (u : U) :
    bananaRetractionLiftLinear i p e (i u) = i (e u) := by
  rw [bananaRetractionLiftLinear_apply, h, i.map_sub]
  abel

/-- The lifted map fixes every vector in the kernel of p. -/
theorem bananaRetractionLiftLinear_on_ker
    (i : U →ₗ[F2] V) (p : V →ₗ[F2] U)
    (e : U →ₗ[F2] U) (x : V)
    (hx : p x = 0) :
    bananaRetractionLiftLinear i p e x = x := by
  simp [bananaRetractionLiftLinear_apply, hx]

/-- A linear automorphism of a retract extends to the ambient
vector space, with the evident inverse and no arbitrary basis
choices. -/
noncomputable def bananaRetractionLiftEquiv
    (i : U →ₗ[F2] V) (p : V →ₗ[F2] U)
    (h : ∀ u, p (i u) = u)
    (e : U ≃ₗ[F2] U) : V ≃ₗ[F2] V where
  toFun := bananaRetractionLiftLinear i p e.toLinearMap
  invFun := bananaRetractionLiftLinear i p e.symm.toLinearMap
  left_inv := by
    intro x
    calc
      bananaRetractionLiftLinear i p e.symm.toLinearMap
          (bananaRetractionLiftLinear i p e.toLinearMap x)
        = (x + i (e (p x) - p x)) +
            i (e.symm (e (p x)) - e (p x)) := by
          rw [bananaRetractionLiftLinear_apply,
            bananaRetractionLiftLinear_project i p h,
            bananaRetractionLiftLinear_apply]
          rfl
      _ = x := by
        rw [e.symm_apply_apply, add_assoc, ← i.map_add]
        have hs : (e (p x) - p x) + (p x - e (p x)) = 0 := by
          abel
        rw [hs, i.map_zero]
        simp
  right_inv := by
    intro x
    calc
      bananaRetractionLiftLinear i p e.toLinearMap
          (bananaRetractionLiftLinear i p e.symm.toLinearMap x)
        = (x + i (e.symm (p x) - p x)) +
            i (e (e.symm (p x)) - e.symm (p x)) := by
          rw [bananaRetractionLiftLinear_apply,
            bananaRetractionLiftLinear_project i p h,
            bananaRetractionLiftLinear_apply]
          rfl
      _ = x := by
        rw [e.apply_symm_apply, add_assoc, ← i.map_add]
        have hs : (e.symm (p x) - p x) +
            (p x - e.symm (p x)) = 0 := by
          abel
        rw [hs, i.map_zero]
        simp
  map_add' := (bananaRetractionLiftLinear i p e.toLinearMap).map_add
  map_smul' := (bananaRetractionLiftLinear i p e.toLinearMap).map_smul

theorem bananaRetractionLiftEquiv_on_range
    (i : U →ₗ[F2] V) (p : V →ₗ[F2] U)
    (h : ∀ u, p (i u) = u)
    (e : U ≃ₗ[F2] U) (u : U) :
    bananaRetractionLiftEquiv i p h e (i u) = i (e u) :=
  bananaRetractionLiftLinear_on_range i p h e.toLinearMap u

end SuccessorTree.NonPrecompact
