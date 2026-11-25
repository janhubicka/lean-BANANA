import BANANA.NonPrecompact.BananaNativePairingEmbedding
import BANANA.NonPrecompact.BananaNativePerfectPairing
import BANANA.NonPrecompact.BananaPerfectTotalDiagramAmalgam
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Native amalgamation of perfect total BANANA systems

Choose perfect pairing coordinates separately on each object and transport the
given embeddings and total maps. The same resulting pair of embeddings works
for each named map, and the maps agree on the actual common native system.
-/

namespace SuccessorTree.NonPrecompact.BananaNative

open Module
open scoped Matrix

variable {L R M N : Type*}
  [AddCommGroup L] [AddCommGroup R] [Module F2 L] [Module F2 R]
  [AddCommGroup M] [AddCommGroup N] [Module F2 M] [Module F2 N]

/-- The standard perfect pairing as a native bilinear map. -/
abbrev standardPairing (d : ℕ) : (Fin d → F2) →ₗ[F2] (Fin d → F2) →ₗ[F2] F2 :=
  dotProductBilin F2 F2

@[simp] theorem standardPairing_apply (d : ℕ) (x y : Fin d → F2) :
    standardPairing d x y = (perfectBanana d).eval x y :=
  (perfectBanana_eval x y).symm

theorem standardPairing_nondegenerate (d : ℕ) : (standardPairing d).Nondegenerate := by
  constructor
  · intro x h
    exact dotProduct_eq_zero x h
  · intro y h
    apply dotProduct_eq_zero
    intro x
    have hx : x ⬝ᵥ y = 0 := h x
    rw [dotProduct_comm y x, hx]

private def inCoordinates {a b : ℕ} {α : L → R → F2} {β : M → N → F2}
    (eA : PairingEquiv α (perfectBanana a).eval)
    (eB : PairingEquiv β (perfectBanana b).eval)
    (f : PairingEmbedding α β) : BananaMatrixEmbedding (perfectBanana a) (perfectBanana b) where
  left := eB.left.toLinearMap.comp (f.left.comp eA.left.symm.toLinearMap)
  right := eB.right.toLinearMap.comp (f.right.comp eA.right.symm.toLinearMap)
  left_injective := eB.left.injective.comp (f.left_injective.comp eA.left.symm.injective)
  right_injective := eB.right.injective.comp (f.right_injective.comp eA.right.symm.injective)
  pairing_apply := by
    intro x y
    change (perfectBanana b).eval (eB.left (f.left (eA.left.symm x)))
      (eB.right (f.right (eA.right.symm y))) = _
    rw [eB.preserves, f.preserves, ← eA.preserves, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply]

private def fromCoordinates {a d : ℕ} {α : L → R → F2}
    (eA : PairingEquiv α (perfectBanana a).eval)
    (f : BananaMatrixEmbedding (perfectBanana a) (perfectBanana d)) :
    PairingEmbedding α (fun x y => standardPairing d x y) where
  left := f.left.comp eA.left.toLinearMap
  right := f.right.comp eA.right.toLinearMap
  left_injective := f.left_injective.comp eA.left.injective
  right_injective := f.right_injective.comp eA.right.injective
  preserves := by
    intro x y
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, standardPairing_apply, f.pairing_apply,
      eA.preserves]

private noncomputable def standardAction {d : ℕ}
    (f : BananaMatrixEmbedding (perfectBanana d) (perfectBanana d)) :
    PairingEquiv (fun x y => standardPairing d x y) (fun x y => standardPairing d x y) where
  left := LinearEquiv.ofInjectiveEndo f.left f.left_injective
  right := LinearEquiv.ofInjectiveEndo f.right f.right_injective
  preserves := by
    intro x y
    change standardPairing d (f.left x) (f.right y) = standardPairing d x y
    simpa only [standardPairing_apply] using f.pairing_apply x y

section

variable [Module.Finite F2 L] [Module.Finite F2 R]

/-- A finite perfect pairing identified with the standard pairing of its rank. -/
noncomputable def perfectPairingEquiv (β : L →ₗ[F2] R →ₗ[F2] F2) (hβ : β.Nondegenerate) :
    PairingEquiv (fun x y => β x y) (perfectBanana (finrank F2 L)).eval where
  left := (Module.finBasis F2 L).equivFun
  right := (LinearEquiv.ofBijective β.flip
    ((nondegenerate_iff_bijective_dual_maps β).mp hβ).2).trans
      (Module.finBasis F2 L).dualBasis.equivFun
  preserves := by
    intro x y
    let b := Module.finBasis F2 L
    have h :
        β x y = ∑ i, b.equivFun x i * β (b i) y := by
      calc
        β x y = β (∑ i, b.equivFun x i • b i) y := by rw [b.sum_equivFun]
        _ = _ := by simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
          smul_eq_mul]
    rw [perfectBanana_eval, h]
    simp only [dotProduct, LinearEquiv.trans_apply, Basis.dualBasis_equivFun]
    rfl

end

section

variable {P Q : Type*}
  [AddCommGroup P] [AddCommGroup Q] [Module F2 P] [Module F2 Q]
  [Module.Finite F2 L] [Module.Finite F2 R] [Module.Finite F2 M] [Module.Finite F2 N]
  [Module.Finite F2 P] [Module.Finite F2 Q]

set_option maxHeartbeats 1100000 in
/-- Two native finite perfect total systems amalgamate over a native perfect
total common system. The result intertwines all the designated automorphisms. -/
theorem exists_native_perfectTotalAmalgam {n : ℕ}
    {α : L →ₗ[F2] R →ₗ[F2] F2} {β : M →ₗ[F2] N →ₗ[F2] F2} {γ : P →ₗ[F2] Q →ₗ[F2] F2}
    (hα : α.Nondegenerate) (hβ : β.Nondegenerate) (hγ : γ.Nondegenerate)
    (f : PairingEmbedding (fun x y => α x y) (fun x y => β x y))
    (g : PairingEmbedding (fun x y => α x y) (fun x y => γ x y))
    (FA : Fin n → PairingEquiv (fun x y => α x y) (fun x y => α x y))
    (FB : Fin n → PairingEquiv (fun x y => β x y) (fun x y => β x y))
    (FC : Fin n → PairingEquiv (fun x y => γ x y) (fun x y => γ x y))
    (hfL : ∀ i x, (FB i).left (f.left x) = f.left ((FA i).left x))
    (hfR : ∀ i y, (FB i).right (f.right y) = f.right ((FA i).right y))
    (hgL : ∀ i x, (FC i).left (g.left x) = g.left ((FA i).left x))
    (hgR : ∀ i y, (FC i).right (g.right y) = g.right ((FA i).right y)) :
    ∃ d : ℕ,
    ∃ f' : PairingEmbedding (fun x y => β x y) (fun x y => standardPairing d x y),
    ∃ g' : PairingEmbedding (fun x y => γ x y) (fun x y => standardPairing d x y),
    ∃ FD : Fin n →
      PairingEquiv (fun x y => standardPairing d x y) (fun x y => standardPairing d x y),
      f'.comp f = g'.comp g ∧
      (∀ i x, (FD i).left (f'.left x) = f'.left ((FB i).left x)) ∧
      (∀ i y, (FD i).right (f'.right y) = f'.right ((FB i).right y)) ∧
      (∀ i x, (FD i).left (g'.left x) = g'.left ((FC i).left x)) ∧
      (∀ i y, (FD i).right (g'.right y) = g'.right ((FC i).right y)) := by
  let eA := perfectPairingEquiv α hα
  let eB := perfectPairingEquiv β hβ
  let eC := perfectPairingEquiv γ hγ
  let f₀ := inCoordinates eA eB f
  let g₀ := inCoordinates eA eC g
  let A₀ (i : Fin n) := inCoordinates eA eA (FA i).toPairingEmbedding
  let B₀ (i : Fin n) := inCoordinates eB eB (FB i).toPairingEmbedding
  let C₀ (i : Fin n) := inCoordinates eC eC (FC i).toPairingEmbedding
  have hLf (i : Fin n) (x : Fin (finrank F2 L) → F2) :
      (B₀ i).left (f₀.left x) = f₀.left ((A₀ i).left x) := by
    change eB.left ((FB i).left (eB.left.symm (eB.left (f.left (eA.left.symm x))))) =
      eB.left (f.left (eA.left.symm (eA.left ((FA i).left (eA.left.symm x)))))
    rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, hfL]
  have hRf (i : Fin n) (x : Fin (finrank F2 L) → F2) :
      (B₀ i).right (f₀.right x) = f₀.right ((A₀ i).right x) := by
    change eB.right ((FB i).right (eB.right.symm (eB.right (f.right (eA.right.symm x))))) =
      eB.right (f.right (eA.right.symm (eA.right ((FA i).right (eA.right.symm x)))))
    rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, hfR]
  have hLg (i : Fin n) (x : Fin (finrank F2 L) → F2) :
      (C₀ i).left (g₀.left x) = g₀.left ((A₀ i).left x) := by
    change eC.left ((FC i).left (eC.left.symm (eC.left (g.left (eA.left.symm x))))) =
      eC.left (g.left (eA.left.symm (eA.left ((FA i).left (eA.left.symm x)))))
    rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, hgL]
  have hRg (i : Fin n) (x : Fin (finrank F2 L) → F2) :
      (C₀ i).right (g₀.right x) = g₀.right ((A₀ i).right x) := by
    change eC.right ((FC i).right (eC.right.symm (eC.right (g.right (eA.right.symm x))))) =
      eC.right (g.right (eA.right.symm (eA.right ((FA i).right (eA.right.symm x)))))
    rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, hgR]
  obtain ⟨d, f₁, g₁, D₁, hL, hR, hfl, hfr, hgl, hgr⟩ :=
    exists_bananaPerfectTotalSystem_perfect_amalgam f₀ g₀ A₀ B₀ C₀ hLf hRf hLg hRg
  refine ⟨d, fromCoordinates eB f₁, fromCoordinates eC g₁, fun i => standardAction (D₁ i),
    ?_, ?_, ?_, ?_, ?_⟩
  · apply PairingEmbedding.ext <;> apply LinearMap.ext <;> intro x
    · simpa only [f₀, g₀, inCoordinates, PairingEmbedding.comp, fromCoordinates,
        LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply] using hL (eA.left x)
    · simpa only [f₀, g₀, inCoordinates, PairingEmbedding.comp, fromCoordinates,
        LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply] using hR (eA.right x)
  · intro i x
    simpa only [B₀, inCoordinates, PairingEquiv.toPairingEmbedding, fromCoordinates, standardAction,
      LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_ofInjectiveEndo,
      LinearEquiv.symm_apply_apply] using hfl i (eB.left x)
  · intro i y
    simpa only [B₀, inCoordinates, PairingEquiv.toPairingEmbedding, fromCoordinates, standardAction,
      LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_ofInjectiveEndo,
      LinearEquiv.symm_apply_apply] using hfr i (eB.right y)
  · intro i x
    simpa only [C₀, inCoordinates, PairingEquiv.toPairingEmbedding, fromCoordinates, standardAction,
      LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_ofInjectiveEndo,
      LinearEquiv.symm_apply_apply] using hgl i (eC.left x)
  · intro i y
    simpa only [C₀, inCoordinates, PairingEquiv.toPairingEmbedding, fromCoordinates, standardAction,
      LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_ofInjectiveEndo,
      LinearEquiv.symm_apply_apply] using hgr i (eC.right y)

end

end SuccessorTree.NonPrecompact.BananaNative
