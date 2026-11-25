import BANANA.NonPrecompact.BananaNativePerfectPairing

/-!
# Perfect-total extensions for native BANANA systems

Finite systems may be given on arbitrary pairs of finite-dimensional vector
spaces. The direct-sum completion of the carrier works simultaneously for
every named partial automorphism.
-/

namespace SuccessorTree.NonPrecompact.BananaNative

open Module LinearMap
open scoped Matrix

variable {L R : Type*}
  [AddCommGroup L] [AddCommGroup R] [Module F2 L] [Module F2 R]

/-- The left inclusion into the perfect completion. -/
abbrev completionLeft : L →ₗ[F2] (L × Dual F2 R) := inl F2 L (Dual F2 R)

/-- The right inclusion into the perfect completion. -/
abbrev completionRight : R →ₗ[F2] (R × Dual F2 L) := inl F2 R (Dual F2 L)

private noncomputable def completionLeftEquiv (U : Submodule F2 L) :
    U ≃ₗ[F2] U.map (completionLeft (R := R)) :=
  (LinearEquiv.ofInjective (completionLeft.comp U.subtype)
      (inl_injective.comp U.injective_subtype)).trans
    (LinearEquiv.ofEq _ _ (by rw [LinearMap.range_comp, Submodule.range_subtype]))

private noncomputable def completionRightEquiv (U : Submodule F2 R) :
    U ≃ₗ[F2] U.map (completionRight (L := L)) :=
  (LinearEquiv.ofInjective (completionRight.comp U.subtype)
      (inl_injective.comp U.injective_subtype)).trans
    (LinearEquiv.ofEq _ _ (by rw [LinearMap.range_comp, Submodule.range_subtype]))

@[simp] private theorem completionLeftEquiv_val (U : Submodule F2 L) (x : U) :
    ((completionLeftEquiv (R := R) U x : U.map completionLeft) : L × Dual F2 R) = ((x : L), 0) :=
  rfl

@[simp] private theorem completionRightEquiv_val (U : Submodule F2 R) (x : U) :
    ((completionRightEquiv (L := L) U x : U.map completionRight) : R × Dual F2 L) = ((x : R), 0) :=
  rfl

private abbrev completeSubpair (U : Subpair L R) :
    Subpair (L × Dual F2 R) (R × Dual F2 L) :=
  (U.1.map completionLeft, U.2.map completionRight)

set_option maxHeartbeats 400000 in
private noncomputable def completePartialIso (β : L →ₗ[F2] R →ₗ[F2] F2)
    {U V : Subpair L R} (p : PartialIso (fun x y => β x y) U V) :
    PartialIso (fun x y => completePairing β x y) (completeSubpair U) (completeSubpair V) where
  left := (completionLeftEquiv U.1).symm.trans (p.left.trans (completionLeftEquiv V.1))
  right := (completionRightEquiv U.2).symm.trans (p.right.trans (completionRightEquiv V.2))
  preserves := by
    intro x y
    obtain ⟨x, rfl⟩ := (completionLeftEquiv U.1).surjective x
    obtain ⟨y, rfl⟩ := (completionRightEquiv U.2).surjective y
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
      completionLeftEquiv_val, completionRightEquiv_val, completePairing_apply,
      LinearMap.zero_apply, add_zero]
    exact p.preserves x y

variable [Module.Finite F2 L] [Module.Finite F2 R]

set_option maxHeartbeats 400000 in
/-- For any finite system, all its named maps extend on the same concrete
perfect completion used in the manuscript. -/
theorem exists_native_perfectTotalExtension {n : ℕ} (β : L →ₗ[F2] R →ₗ[F2] F2)
    (U V : Fin n → Subpair L R) (p : ∀ i, PartialIso (fun x y => β x y) (U i) (V i)) :
    ∃ q : Fin n → PairingEquiv (fun x y => completePairing β x y) (fun x y => completePairing β x y),
      (∀ i (x : (U i).1), (q i).left ((x : L), 0) = (((p i).left x : L), 0)) ∧
      (∀ i (y : (U i).2), (q i).right ((y : R), 0) = (((p i).right y : R), 0)) := by
  have hext (i : Fin n) :=
    exists_native_perfectAutomorphism_extends (completePairing β) (completePairing_nondegenerate β)
      (completePartialIso β (p i))
  choose q hl hr using hext
  refine ⟨q, ?_, ?_⟩
  · intro i x
    have h := hl i (completionLeftEquiv (U i).1 x)
    simpa only [completePartialIso, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
      completionLeftEquiv_val] using h
  · intro i y
    have h := hr i (completionRightEquiv (U i).2 y)
    simpa only [completePartialIso, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
      completionRightEquiv_val] using h

end SuccessorTree.NonPrecompact.BananaNative
