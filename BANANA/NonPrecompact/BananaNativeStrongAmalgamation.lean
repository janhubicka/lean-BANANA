import BANANA.NonPrecompact.BananaNativePairingEmbedding
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Strong amalgamation of native BANANA pairings

Choose complements to the two images of the common source, separately on
each sort. Combine the old pairings on the common direct-sum coordinates,
subtracting their common restriction once. The two mixed complement
pairings vanish and the new inclusions meet exactly in the source.
-/

namespace SuccessorTree.NonPrecompact.BananaNative

open LinearMap

variable {AL AR BL BR CL CR DL DR : Type*}
  [AddCommGroup AL] [AddCommGroup AR] [Module F2 AL] [Module F2 AR]
  [AddCommGroup BL] [AddCommGroup BR] [Module F2 BL] [Module F2 BR]
  [AddCommGroup CL] [AddCommGroup CR] [Module F2 CL] [Module F2 CR]
  [AddCommGroup DL] [AddCommGroup DR] [Module F2 DL] [Module F2 DR]

/-- The two embeddings agree over the source and introduce no further
identifications on either sort. -/
structure IsStrongAmalgam
    {α : AL → AR → F2} {β : BL → BR → F2} {γ : CL → CR → F2} {δ : DL → DR → F2}
    (f : PairingEmbedding α β) (g : PairingEmbedding α γ)
    (iB : PairingEmbedding β δ) (iC : PairingEmbedding γ δ) : Prop where
  comm_left : iB.left.comp f.left = iC.left.comp g.left
  comm_right : iB.right.comp f.right = iC.right.comp g.right
  intersection_left (x : BL) (y : CL) :
    iB.left x = iC.left y ↔ ∃ z, x = f.left z ∧ y = g.left z
  intersection_right (x : BR) (y : CR) :
    iB.right x = iC.right y ↔ ∃ z, x = f.right z ∧ y = g.right z

namespace IsStrongAmalgam

variable {α : AL → AR → F2} {β : BL → BR → F2}
  {γ : CL → CR → F2} {δ : DL → DR → F2}
  {f : PairingEmbedding α β} {g : PairingEmbedding α γ}
  {iB : PairingEmbedding β δ} {iC : PairingEmbedding γ δ}

/-- Strong intersection as an equality of left-sort image subspaces. -/
theorem range_inter_left (h : IsStrongAmalgam f g iB iC) :
    LinearMap.range iB.left ⊓ LinearMap.range iC.left =
      LinearMap.range (iB.left.comp f.left) := by
  ext z
  constructor
  · rintro ⟨⟨x, rfl⟩, ⟨y, hxy⟩⟩
    obtain ⟨a, rfl, _⟩ := (h.intersection_left x y).1 hxy.symm
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨⟨f.left a, rfl⟩, ⟨g.left a, (LinearMap.congr_fun h.comm_left a).symm⟩⟩

/-- Strong intersection as an equality of right-sort image subspaces. -/
theorem range_inter_right (h : IsStrongAmalgam f g iB iC) :
    LinearMap.range iB.right ⊓ LinearMap.range iC.right =
      LinearMap.range (iB.right.comp f.right) := by
  ext z
  constructor
  · rintro ⟨⟨x, rfl⟩, ⟨y, hxy⟩⟩
    obtain ⟨a, rfl, _⟩ := (h.intersection_right x y).1 hxy.symm
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨⟨f.right a, rfl⟩, ⟨g.right a, (LinearMap.congr_fun h.comm_right a).symm⟩⟩

end IsStrongAmalgam

section Split

variable {A X Y B C : Type*}
  [AddCommGroup A] [AddCommGroup X] [AddCommGroup Y] [AddCommGroup B] [AddCommGroup C]
  [Module F2 A] [Module F2 X] [Module F2 Y] [Module F2 B] [Module F2 C]

private noncomputable def splitEquiv (f : A →ₗ[F2] B) (hf : Function.Injective f)
    (U : Submodule F2 B) (hU : IsCompl (LinearMap.range f) U) : (A × U) ≃ₗ[F2] B :=
  ((LinearEquiv.ofInjective f hf).prodCongr (LinearEquiv.refl F2 U)).trans
    (Submodule.prodEquivOfIsCompl _ _ hU)

private theorem splitEquiv_apply (f : A →ₗ[F2] B) (hf : Function.Injective f)
    (U : Submodule F2 B) (hU : IsCompl (LinearMap.range f) U) (a : A) (u : U) :
    splitEquiv f hf U hU (a, u) = f a + u :=
  rfl

private def intoB (e : (A × X) ≃ₗ[F2] B) : B →ₗ[F2] (A × X × Y) :=
  (LinearMap.prodMap LinearMap.id (LinearMap.inl F2 X Y)).comp e.symm.toLinearMap

private def intoC (e : (A × Y) ≃ₗ[F2] C) : C →ₗ[F2] (A × X × Y) :=
  (LinearMap.prodMap LinearMap.id (LinearMap.inr F2 X Y)).comp e.symm.toLinearMap

private def toB (e : (A × X) ≃ₗ[F2] B) : (A × X × Y) →ₗ[F2] B :=
  e.toLinearMap.comp (LinearMap.prodMap LinearMap.id (LinearMap.fst F2 X Y))

private def toC (e : (A × Y) ≃ₗ[F2] C) : (A × X × Y) →ₗ[F2] C :=
  e.toLinearMap.comp (LinearMap.prodMap LinearMap.id (LinearMap.snd F2 X Y))

private theorem intoB_apply (e : (A × X) ≃ₗ[F2] B) (b : B) :
    intoB (Y := Y) e b = ((e.symm b).1, (e.symm b).2, 0) := rfl

private theorem intoC_apply (e : (A × Y) ≃ₗ[F2] C) (c : C) :
    intoC (X := X) e c = ((e.symm c).1, 0, (e.symm c).2) := rfl

private theorem toB_apply (e : (A × X) ≃ₗ[F2] B) (a : A) (x : X) (y : Y) :
    toB e (a, x, y) = e (a, x) := rfl

private theorem toC_apply (e : (A × Y) ≃ₗ[F2] C) (a : A) (x : X) (y : Y) :
    toC e (a, x, y) = e (a, y) := rfl

private theorem toB_intoB (e : (A × X) ≃ₗ[F2] B) (b : B) :
    toB e (intoB (Y := Y) e b) = b := by
  simp [intoB_apply, toB_apply]

private theorem toC_intoC (e : (A × Y) ≃ₗ[F2] C) (c : C) :
    toC e (intoC (X := X) e c) = c := by
  simp [intoC_apply, toC_apply]

private theorem intoB_eq_intoC (eB : (A × X) ≃ₗ[F2] B) (eC : (A × Y) ≃ₗ[F2] C)
    (b : B) (c : C) :
    intoB (Y := Y) eB b = intoC (X := X) eC c ↔
      ∃ a, b = eB (a, 0) ∧ c = eC (a, 0) := by
  constructor
  · intro h
    simp only [intoB_apply, intoC_apply, Prod.mk.injEq] at h
    obtain ⟨hA, hX, hY⟩ := h
    refine ⟨(eB.symm b).1, ?_, ?_⟩
    · exact (eB.apply_symm_apply b).symm.trans (congrArg eB (Prod.ext rfl hX))
    · exact (eC.apply_symm_apply c).symm.trans (congrArg eC (Prod.ext hA.symm hY.symm))
  · rintro ⟨a, rfl, rfl⟩
    simp [intoB_apply, intoC_apply]

end Split

/-- The manuscript's direct-sum strong amalgam for arbitrary BANANA embeddings.
The first and second added summands are the complementary subspaces in the
two targets. The pairing vanishes between complements on opposite branches. -/
theorem exists_strongAmalgam
    (α : AL →ₗ[F2] AR →ₗ[F2] F2) (β : BL →ₗ[F2] BR →ₗ[F2] F2)
    (γ : CL →ₗ[F2] CR →ₗ[F2] F2)
    (f : PairingEmbedding (fun x y => α x y) (fun x y => β x y))
    (g : PairingEmbedding (fun x y => α x y) (fun x y => γ x y)) :
    ∃ (UB : Submodule F2 BL) (VB : Submodule F2 BR)
      (UC : Submodule F2 CL) (VC : Submodule F2 CR),
      IsCompl (LinearMap.range f.left) UB ∧ IsCompl (LinearMap.range f.right) VB ∧
      IsCompl (LinearMap.range g.left) UC ∧ IsCompl (LinearMap.range g.right) VC ∧
      ∃ (δ : (AL × UB × UC) →ₗ[F2] (AR × VB × VC) →ₗ[F2] F2)
        (iB : PairingEmbedding (fun x y => β x y) (fun x y => δ x y))
        (iC : PairingEmbedding (fun x y => γ x y) (fun x y => δ x y)),
        IsStrongAmalgam f g iB iC ∧
        (∀ (x : UB) (y : VC), δ (0, x, 0) (0, 0, y) = 0) ∧
        (∀ (x : UC) (y : VB), δ (0, 0, x) (0, y, 0) = 0) := by
  obtain ⟨UB, hUB⟩ := Submodule.exists_isCompl (LinearMap.range f.left)
  obtain ⟨VB, hVB⟩ := Submodule.exists_isCompl (LinearMap.range f.right)
  obtain ⟨UC, hUC⟩ := Submodule.exists_isCompl (LinearMap.range g.left)
  obtain ⟨VC, hVC⟩ := Submodule.exists_isCompl (LinearMap.range g.right)
  let bL := splitEquiv f.left f.left_injective UB hUB
  let bR := splitEquiv f.right f.right_injective VB hVB
  let cL := splitEquiv g.left g.left_injective UC hUC
  let cR := splitEquiv g.right g.right_injective VC hVC
  have hbL a : bL (a, 0) = f.left a := by simp [bL, splitEquiv_apply]
  have hbR a : bR (a, 0) = f.right a := by simp [bR, splitEquiv_apply]
  have hcL a : cL (a, 0) = g.left a := by simp [cL, splitEquiv_apply]
  have hcR a : cR (a, 0) = g.right a := by simp [cR, splitEquiv_apply]
  let δ : (AL × UB × UC) →ₗ[F2] (AR × VB × VC) →ₗ[F2] F2 :=
    β.compl₁₂ (toB bL) (toB bR) + γ.compl₁₂ (toC cL) (toC cR) -
      α.compl₁₂ (LinearMap.fst F2 AL (UB × UC)) (LinearMap.fst F2 AR (VB × VC))
  let iB : PairingEmbedding (fun x y => β x y) (fun x y => δ x y) := {
    left := intoB bL
    right := intoB bR
    left_injective := (show Function.LeftInverse (toB bL) (intoB (Y := UC) bL) from
      toB_intoB bL).injective
    right_injective := (show Function.LeftInverse (toB bR) (intoB (Y := VC) bR) from
      toB_intoB bR).injective
    preserves := by
      intro x y
      simp [δ, intoB_apply, toB_apply, toC_apply, hcL, hcR, g.preserves] }
  let iC : PairingEmbedding (fun x y => γ x y) (fun x y => δ x y) := {
    left := intoC cL
    right := intoC cR
    left_injective := (show Function.LeftInverse (toC cL) (intoC (X := UB) cL) from
      toC_intoC cL).injective
    right_injective := (show Function.LeftInverse (toC cR) (intoC (X := VB) cR) from
      toC_intoC cR).injective
    preserves := by
      intro x y
      simp [δ, intoC_apply, toB_apply, toC_apply, hbL, hbR, f.preserves, add_sub_cancel_left] }
  have hL (x : BL) (y : CL) :
      iB.left x = iC.left y ↔ ∃ a, x = f.left a ∧ y = g.left a := by
    change intoB bL x = intoC cL y ↔ _
    simpa only [hbL, hcL] using intoB_eq_intoC bL cL x y
  have hR (x : BR) (y : CR) :
      iB.right x = iC.right y ↔ ∃ a, x = f.right a ∧ y = g.right a := by
    change intoB bR x = intoC cR y ↔ _
    simpa only [hbR, hcR] using intoB_eq_intoC bR cR x y
  refine ⟨UB, VB, UC, VC, hUB, hVB, hUC, hVC, δ, iB, iC, ⟨?_, ?_, hL, hR⟩, ?_, ?_⟩
  · apply LinearMap.ext
    intro a
    exact (hL _ _).2 ⟨a, rfl, rfl⟩
  · apply LinearMap.ext
    intro a
    exact (hR _ _).2 ⟨a, rfl, rfl⟩
  · intro x y
    simp [δ, toB_apply, toC_apply, hbR, hcL]
  · intro x y
    simp [δ, toB_apply, toC_apply, hbL, hcR]

/-- Joint embedding of native pairings, using disjoint coordinates and zero
cross-pairings. This is amalgamation over the zero spaces. -/
theorem exists_jointEmbedding
    (β : BL →ₗ[F2] BR →ₗ[F2] F2) (γ : CL →ₗ[F2] CR →ₗ[F2] F2) :
    ∃ δ : (BL × CL) →ₗ[F2] (BR × CR) →ₗ[F2] F2,
      Nonempty (PairingEmbedding (fun x y => β x y) (fun x y => δ x y)) ∧
      Nonempty (PairingEmbedding (fun x y => γ x y) (fun x y => δ x y)) := by
  let δ := β.compl₁₂ (LinearMap.fst F2 BL CL) (LinearMap.fst F2 BR CR) +
    γ.compl₁₂ (LinearMap.snd F2 BL CL) (LinearMap.snd F2 BR CR)
  refine ⟨δ, ⟨⟨inl F2 BL CL, inl F2 BR CR, inl_injective, inl_injective, ?_⟩⟩,
    ⟨⟨inr F2 BL CL, inr F2 BR CR, inr_injective, inr_injective, ?_⟩⟩⟩
  · intro x y
    simp [δ]
  · intro x y
    simp [δ]


/-- The native amalgam as a pair of finite vector spaces with all instance
data available to the caller. -/
theorem exists_finiteStrongAmalgam
    {A₁ A₂ B₁ B₂ C₁ C₂ : Type}
    [AddCommGroup A₁] [Module F2 A₁] [Finite A₁]
    [AddCommGroup A₂] [Module F2 A₂] [Finite A₂]
    [AddCommGroup B₁] [Module F2 B₁] [Finite B₁]
    [AddCommGroup B₂] [Module F2 B₂] [Finite B₂]
    [AddCommGroup C₁] [Module F2 C₁] [Finite C₁]
    [AddCommGroup C₂] [Module F2 C₂] [Finite C₂]
    (α : A₁ →ₗ[F2] A₂ →ₗ[F2] F2) (β : B₁ →ₗ[F2] B₂ →ₗ[F2] F2)
    (γ : C₁ →ₗ[F2] C₂ →ₗ[F2] F2)
    (f : PairingEmbedding (fun x y => α x y) (fun x y => β x y))
    (g : PairingEmbedding (fun x y => α x y) (fun x y => γ x y)) :
    ∃ (D₁ D₂ : Type) (_ : AddCommGroup D₁) (_ : AddCommGroup D₂)
      (_ : Module F2 D₁) (_ : Module F2 D₂),
      Finite D₁ ∧ Finite D₂ ∧
      ∃ (δ : D₁ →ₗ[F2] D₂ →ₗ[F2] F2)
        (iB : PairingEmbedding (fun x y => β x y) (fun x y => δ x y))
        (iC : PairingEmbedding (fun x y => γ x y) (fun x y => δ x y)),
        IsStrongAmalgam f g iB iC := by
  obtain ⟨X, Y, U, V, -, -, -, -, δ, iB, iC, h, -, -⟩ :=
    exists_strongAmalgam α β γ f g
  exact ⟨A₁ × X × U, A₂ × Y × V, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, δ, iB, iC, h⟩

end SuccessorTree.NonPrecompact.BananaNative
