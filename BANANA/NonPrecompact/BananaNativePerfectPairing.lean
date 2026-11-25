import BANANA.NonPrecompact.BananaNativeCoherentEppa
import BANANA.NonPrecompact.LinearExtension
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Completion and homogeneity of finite BANANA pairings

The arguments use the original two vector spaces and their duals. Mathlib's
nondegeneracy and flip lemmas identify each side of a perfect pairing with
the dual of the other.
-/

namespace SuccessorTree.NonPrecompact.BananaNative

open Module LinearMap

variable {L R : Type*}
  [AddCommGroup L] [AddCommGroup R] [Module F2 L] [Module F2 R]

/-- The manuscript's perfect completion on the products with the duals. -/
def completePairing (β : L →ₗ[F2] R →ₗ[F2] F2) :
    (L × Dual F2 R) →ₗ[F2] (R × Dual F2 L) →ₗ[F2] F2 :=
  β.compl₁₂ (fst F2 L (Dual F2 R)) (fst F2 R (Dual F2 L)) +
  (Dual.eval F2 R).flip.compl₁₂ (snd F2 L (Dual F2 R)) (fst F2 R (Dual F2 L)) +
  (Dual.eval F2 L).compl₁₂ (fst F2 L (Dual F2 R)) (snd F2 R (Dual F2 L))

@[simp]
theorem completePairing_apply (β : L →ₗ[F2] R →ₗ[F2] F2)
    (x : L) (α : Dual F2 R) (y : R) (φ : Dual F2 L) :
    completePairing β (x, α) (y, φ) = β x y + α y + φ x := rfl

/-- Evaluating first against a dual element and then against a vector,
and symmetrically on the other side, shows nondegeneracy. -/
theorem completePairing_nondegenerate (β : L →ₗ[F2] R →ₗ[F2] F2) :
    (completePairing β).Nondegenerate := by
  constructor
  · rintro ⟨x, α⟩ h
    have hx : x = 0 := by
      apply (Module.eval_apply_eq_zero_iff F2 x).mp
      ext φ
      simpa using h (0, φ)
    subst x
    have hα : α = 0 := by
      ext y
      simpa using h (y, 0)
    simp [hα]
  · rintro ⟨y, φ⟩ h
    have hy : y = 0 := by
      apply (Module.eval_apply_eq_zero_iff F2 y).mp
      ext α
      simpa using h (0, α)
    subst y
    have hφ : φ = 0 := by
      ext x
      simpa using h (x, 0)
    simp [hφ]

variable [Module.Finite F2 L] [Module.Finite F2 R]

/-- The canonical inclusions into the concrete perfect completion preserve
the original pairing, and both completed sorts have the sum dimension. -/
theorem exists_native_perfectCompletion (β : L →ₗ[F2] R →ₗ[F2] F2) :
    (completePairing β).Nondegenerate ∧
    finrank F2 (L × Dual F2 R) = finrank F2 L + finrank F2 R ∧
    finrank F2 (R × Dual F2 L) = finrank F2 L + finrank F2 R ∧
    ∃ (f : L →ₗ[F2] (L × Dual F2 R)) (g : R →ₗ[F2] (R × Dual F2 L)),
      Function.Injective f ∧ Function.Injective g ∧
        ∀ x y, completePairing β (f x) (g y) = β x y := by
  refine ⟨completePairing_nondegenerate β, ?_, ?_,
    inl F2 L (Dual F2 R), inl F2 R (Dual F2 L), inl_injective, inl_injective, ?_⟩
  · simp [Module.finrank_prod, Subspace.dual_finrank_eq]
  · simp [Module.finrank_prod, Subspace.dual_finrank_eq, add_comm]
  · intro x y
    change completePairing β (x, 0) (y, 0) = β x y
    simp

omit [Module.Finite F2 R] in
/-- The two maps to the dual spaces are isomorphisms exactly when the finite
pairing is nondegenerate. -/
theorem nondegenerate_iff_bijective_dual_maps (β : L →ₗ[F2] R →ₗ[F2] F2) :
    β.Nondegenerate ↔ Function.Bijective β ∧ Function.Bijective β.flip := by
  rw [LinearMap.Nondegenerate, separatingLeft_iff_ker_eq_bot,
    separatingRight_iff_flip_ker_eq_bot, ker_eq_bot, ker_eq_bot]
  exact ⟨fun ⟨hl, hr⟩ => ⟨⟨hl, flip_injective_iff₁.mp hr⟩, ⟨hr, flip_surjective_iff₁.mpr hl⟩⟩,
    fun ⟨hl, hr⟩ => ⟨hl.1, hr.1⟩⟩

/-- Each isomorphism between substructures of a finite perfect pairing
extends to an automorphism of the ambient pairing. -/
theorem exists_native_perfectAutomorphism_extends (β : L →ₗ[F2] R →ₗ[F2] F2)
    (hβ : β.Nondegenerate) {U V : Subpair L R}
    (p : PartialIso (fun x y => β x y) U V) :
    ∃ H : PairingEquiv (fun x y => β x y) (fun x y => β x y),
      (∀ x : U.1, H.left x = p.left x) ∧ (∀ y : U.2, H.right y = p.right y) := by
  obtain ⟨hL, hR⟩ := (nondegenerate_iff_bijective_dual_maps β).mp hβ
  let e : U.2 →ₗ[F2] R := V.2.subtype.comp p.right.toLinearMap
  let q := U.2.subtype.dualMap.comp β
  let q' := e.dualMap.comp β
  have hq : Function.Surjective q :=
    (dualMap_surjective_iff.mpr U.2.injective_subtype).comp hL.2
  have he : Function.Injective e :=
    V.2.injective_subtype.comp p.right.injective
  have hq' : Function.Surjective q' :=
    (dualMap_surjective_iff.mpr he).comp hL.2
  have hpartial (x : U.1) : q' (p.left x) = q x := by
    ext y
    exact p.preserves x y
  obtain ⟨h, hl, hquot⟩ := exists_linearEquiv_extends_of_surjective q q' hq hq' p.left hpartial
  let ψ : R ≃ₗ[F2] Dual F2 L := LinearEquiv.ofBijective β.flip hR
  let k : R ≃ₗ[F2] R := (ψ.trans h.symm.dualMap).trans ψ.symm
  have hk (x : L) (y : R) : β (h x) (k y) = β x y := by
    change (ψ (ψ.symm (h.symm.dualMap (ψ y)))) (h x) = (ψ y) x
    rw [ψ.apply_symm_apply, LinearEquiv.dualMap_apply, h.symm_apply_apply]
  refine ⟨⟨h, k, hk⟩, hl, ?_⟩
  intro y
  apply ψ.injective
  ext z
  obtain ⟨x, rfl⟩ := h.surjective z
  change β (h x) (k y) = β (h x) (p.right y)
  rw [hk]
  exact (congrArg (fun φ : Dual F2 U.2 => φ y)
    (LinearMap.congr_fun hquot x)).symm

end SuccessorTree.NonPrecompact.BananaNative
