import BANANA.NonPrecompact.CoherentEppaWitness
import Mathlib.LinearAlgebra.Basis.Bilinear
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Coherent EPPA for arbitrary finite BANANA pairings

The matrix theorem transports to any pair of finite-dimensional vector
spaces by choosing bases on the two sorts. Partial isomorphisms are
conjugated between the exact subspaces, so their composition and the
single coherent extension assignment are preserved.
-/

namespace SuccessorTree.NonPrecompact.BananaNative

open Module
open scoped Matrix

variable {L R L' R' L'' R'' : Type*}
  [AddCommGroup L] [AddCommGroup R] [Module F2 L] [Module F2 R]
  [AddCommGroup L'] [AddCommGroup R'] [Module F2 L'] [Module F2 R']
  [AddCommGroup L''] [AddCommGroup R''] [Module F2 L''] [Module F2 R'']

/-- Sortwise linear isomorphisms preserving the pairing. -/
structure PairingEquiv (β : L → R → F2) (γ : L' → R' → F2) where
  left : L ≃ₗ[F2] L'
  right : R ≃ₗ[F2] R'
  preserves : ∀ x y, γ (left x) (right y) = β x y

namespace PairingEquiv

/-- The identity isomorphism of a pairing. -/
protected def refl (β : L → R → F2) : PairingEquiv β β where
  left := LinearEquiv.refl _ _
  right := LinearEquiv.refl _ _
  preserves _ _ := rfl

/-- Compose two pairing isomorphisms. -/
protected def trans {β : L → R → F2} {γ : L' → R' → F2} {δ : L'' → R'' → F2}
    (f : PairingEquiv β γ) (g : PairingEquiv γ δ) : PairingEquiv β δ where
  left := f.left.trans g.left
  right := f.right.trans g.right
  preserves x y := (g.preserves _ _).trans (f.preserves x y)

@[ext]
theorem ext {β : L → R → F2} {γ : L' → R' → F2} {f g : PairingEquiv β γ}
    (hl : f.left = g.left) (hr : f.right = g.right) : f = g := by
  cases f
  cases g
  cases hl
  cases hr
  rfl

end PairingEquiv

/-- A finite BANANA substructure is given by its two subspaces. -/
abbrev Subpair (L R : Type*) [AddCommGroup L] [AddCommGroup R] [Module F2 L] [Module F2 R] :=
  Submodule F2 L × Submodule F2 R

/-- An isomorphism of two substructures with the restricted ambient pairing. -/
abbrev PartialIso (β : L → R → F2) (U V : Subpair L R) :=
  PairingEquiv (fun (x : U.1) (y : U.2) => β x y) (fun (x : V.1) (y : V.2) => β x y)

/-- The pairing matrix obtained from bases of the two native sorts. -/
noncomputable def coordinates {l r : ℕ} (β : L →ₗ[F2] R →ₗ[F2] F2)
    (bL : Basis (Fin l) F2 L) (bR : Basis (Fin r) F2 R) : BananaMatrixStructure l r :=
  ⟨fun i j => β (bL i) (bR j)⟩

/-- Evaluating that matrix on coordinate vectors recovers the native pairing. -/
theorem coordinates_eval {l r : ℕ} (β : L →ₗ[F2] R →ₗ[F2] F2)
    (bL : Basis (Fin l) F2 L) (bR : Basis (Fin r) F2 R) (x : L) (y : R) :
    (coordinates β bL bR).eval (bL.equivFun x) (bR.equivFun y) = β x y := by
  symm
  calc
    β x y =
        β (∑ i, bL.equivFun x i • bL i) (∑ j, bR.equivFun y j • bR j) := by
        rw [bL.sum_equivFun, bR.sum_equivFun]
    _ = (coordinates β bL bR).eval (bL.equivFun x) (bR.equivFun y) := by
      simp only [BananaMatrixStructure.eval, Matrix.mulVec, dotProduct, coordinates,
        map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
      simp_rw [Finset.mul_sum]
      conv_lhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ac_rfl

private noncomputable def coordSubpair {l r : ℕ}
    (bL : Basis (Fin l) F2 L) (bR : Basis (Fin r) F2 R) (U : Subpair L R) :
    BananaSubpair l r where
  left := U.1.map bL.equivFun.toLinearMap
  right := U.2.map bR.equivFun.toLinearMap

private noncomputable def coordIso {l r : ℕ} (β : L →ₗ[F2] R →ₗ[F2] F2)
    (bL : Basis (Fin l) F2 L) (bR : Basis (Fin r) F2 R) {U V : Subpair L R}
    (p : PartialIso (fun x y => β x y) U V) :
    BananaSubpair.Iso (coordinates β bL bR) (coordSubpair bL bR U) (coordSubpair bL bR V) where
  left := ((bL.equivFun.submoduleMap U.1).symm.trans p.left).trans
    (bL.equivFun.submoduleMap V.1)
  right := ((bR.equivFun.submoduleMap U.2).symm.trans p.right).trans
    (bR.equivFun.submoduleMap V.2)
  pairing_apply x y := by
    obtain ⟨x', rfl⟩ := (bL.equivFun.submoduleMap U.1).surjective x
    obtain ⟨y', rfl⟩ := (bR.equivFun.submoduleMap U.2).surjective y
    change (coordinates β bL bR).eval
        (bL.equivFun (p.left ((bL.equivFun.submoduleMap U.1).symm
          (bL.equivFun.submoduleMap U.1 x'))))
        (bR.equivFun (p.right ((bR.equivFun.submoduleMap U.2).symm
          (bR.equivFun.submoduleMap U.2 y')))) =
      (coordinates β bL bR).eval (bL.equivFun x') (bR.equivFun y')
    rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply,
      coordinates_eval, coordinates_eval]
    exact p.preserves x' y'

private theorem coordIso_ext {l r : ℕ} {A : BananaMatrixStructure l r}
    {U V : BananaSubpair l r} {p q : BananaSubpair.Iso A U V}
    (hl : p.left = q.left) (hr : p.right = q.right) : p = q := by
  cases p
  cases q
  cases hl
  cases hr
  rfl

private theorem coordIso_refl {l r : ℕ} (β : L →ₗ[F2] R →ₗ[F2] F2)
    (bL : Basis (Fin l) F2 L) (bR : Basis (Fin r) F2 R) (U : Subpair L R) :
    coordIso β bL bR (PairingEquiv.refl (fun (x : U.1) (y : U.2) => β x y)) =
      BananaSubpair.Iso.refl _ (coordSubpair bL bR U) := by
  apply coordIso_ext <;> apply LinearEquiv.ext <;> intro x
  · exact (bL.equivFun.submoduleMap U.1).apply_symm_apply x
  · exact (bR.equivFun.submoduleMap U.2).apply_symm_apply x

private theorem coordIso_trans {l r : ℕ} (β : L →ₗ[F2] R →ₗ[F2] F2)
    (bL : Basis (Fin l) F2 L) (bR : Basis (Fin r) F2 R) {U V T : Subpair L R}
    (p : PartialIso (fun x y => β x y) U V) (q : PartialIso (fun x y => β x y) V T) :
    coordIso β bL bR (p.trans q) = (coordIso β bL bR p).trans (coordIso β bL bR q) := by
  apply coordIso_ext <;> apply LinearEquiv.ext <;> intro x
  · let eU := bL.equivFun.submoduleMap U.1
    let eV := bL.equivFun.submoduleMap V.1
    let eT := bL.equivFun.submoduleMap T.1
    change eT (q.left (p.left (eU.symm x))) =
      eT (q.left (eV.symm (eV (p.left (eU.symm x)))))
    rw [LinearEquiv.symm_apply_apply]
  · let eU := bR.equivFun.submoduleMap U.2
    let eV := bR.equivFun.submoduleMap V.2
    let eT := bR.equivFun.submoduleMap T.2
    change eT (q.right (p.right (eU.symm x))) =
      eT (q.right (eV.symm (eV (p.right (eU.symm x)))))
    rw [LinearEquiv.symm_apply_apply]

private noncomputable def perfectEquiv {d : ℕ}
    (f : BananaMatrixEmbedding (perfectBanana d) (perfectBanana d)) :
    PairingEquiv (perfectBanana d).eval (perfectBanana d).eval where
  left := LinearEquiv.ofInjectiveEndo f.left f.left_injective
  right := LinearEquiv.ofInjectiveEndo f.right f.right_injective
  preserves := f.pairing_apply

/-- Coherent EPPA for a bilinear pairing on arbitrary finite-dimensional
F₂-vector spaces. The perfect witness uses two copies of the standard
coordinate space of dimension equal to the sum of the two dimensions. -/
theorem exists_coherentEppaWitness [Module.Finite F2 L] [Module.Finite F2 R]
    (β : L →ₗ[F2] R →ₗ[F2] F2) :
    let d := finrank F2 L + finrank F2 R
    let W := Fin d → F2
    let γ := (perfectBanana d).eval
    ∃ (f : L →ₗ[F2] W) (g : R →ₗ[F2] W)
      (Θ : ∀ U V : Subpair L R, PartialIso (fun x y => β x y) U V → PairingEquiv γ γ),
      Function.Injective f ∧ Function.Injective g ∧
      (∀ x y, γ (f x) (g y) = β x y) ∧
      (∀ U V (p : PartialIso (fun x y => β x y) U V) (x : U.1),
        (Θ U V p).left (f x) = f (p.left x)) ∧
      (∀ U V (p : PartialIso (fun x y => β x y) U V) (y : U.2),
        (Θ U V p).right (g y) = g (p.right y)) ∧
      (∀ U, Θ U U (PairingEquiv.refl (fun (x : U.1) (y : U.2) => β x y)) =
        PairingEquiv.refl γ) ∧
      (∀ U V T (p : PartialIso (fun x y => β x y) U V)
        (q : PartialIso (fun x y => β x y) V T),
        Θ U T (p.trans q) = (Θ U V p).trans (Θ V T q)) := by
  dsimp only
  let bL := Module.finBasis F2 L
  let bR := Module.finBasis F2 R
  let A := coordinates β bL bR
  obtain ⟨θ, hL, hR, hId, hComp⟩ := A.exists_coherentEppaWitness
  let f := A.completionEmbedding.left.comp bL.equivFun.toLinearMap
  let g := A.completionEmbedding.right.comp bR.equivFun.toLinearMap
  refine ⟨f, g, fun U V p => perfectEquiv (θ _ _ (coordIso β bL bR p)), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact A.completionEmbedding.left_injective.comp bL.equivFun.injective
  · exact A.completionEmbedding.right_injective.comp bR.equivFun.injective
  · intro x y
    exact (A.completionEmbedding.pairing_apply (bL.equivFun x) (bR.equivFun y)).trans
      (coordinates_eval β bL bR x y)
  · intro U V p x
    let p' := coordIso β bL bR p
    let e := bL.equivFun.submoduleMap U.1
    have h := hL _ _ p' (e x)
    change (θ _ _ p').left (A.completionLeft (bL.equivFun x)) =
      A.completionLeft (bL.equivFun (p.left (e.symm (e x)))) at h
    rw [LinearEquiv.symm_apply_apply] at h
    exact h
  · intro U V p y
    let p' := coordIso β bL bR p
    let e := bR.equivFun.submoduleMap U.2
    have h := hR _ _ p' (e y)
    change (θ _ _ p').right (A.completionRight (bR.equivFun y)) =
      A.completionRight (bR.equivFun (p.right (e.symm (e y)))) at h
    rw [LinearEquiv.symm_apply_apply] at h
    exact h
  · intro U
    dsimp only
    rw [coordIso_refl, hId]
    apply PairingEquiv.ext <;> apply LinearEquiv.ext <;> intro x <;> rfl
  · intro U V T p q
    dsimp only
    rw [coordIso_trans, hComp]
    apply PairingEquiv.ext <;> apply LinearEquiv.ext <;> intro x <;> rfl

end SuccessorTree.NonPrecompact.BananaNative
