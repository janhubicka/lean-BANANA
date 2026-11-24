import BANANA.NonPrecompact.QuadraticResidueStandard
import BANANA.NonPrecompact.SymplecticQuadraticPolar
import BANANA.NonPrecompact.SymplecticSlice

/-!
# Persistent point colourings of finite alternating spaces

One colouring of the ambient nonzero vectors realises every colour in
every nondegenerate subspace of the prescribed dimension. Over `F₂` a
one-dimensional subspace has a unique nonzero vector.
-/

namespace SuccessorTree.NonPrecompact

open scoped BigOperators Matrix
open LinearMap Module Submodule

/-- The integer weight of the strict upper triangular quadratic expression. -/
private def pointWeight {n : ℕ} (M : Matrix (Fin n) (Fin n) F2) (x : Fin n → F2) : ℕ :=
  ∑ i, ∑ j, (strictUpper M i j * x i * x j).val

private theorem cast_pointWeight {n : ℕ} (M : Matrix (Fin n) (Fin n) F2)
    (x : Fin n → F2) : (pointWeight M x : F2) = upperQuadratic M x := by
  simp only [pointWeight, Nat.cast_sum, ZMod.natCast_zmod_val, upperQuadratic,
    LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toBilin'_apply, mul_comm (strictUpper M _ _)]

private theorem affineBit_of_linearMap {d n m : ℕ}
    (L : (Fin d → F2) →ₗ[F2] (Fin n → F2)) (w : Fin n → F2)
    (j : Fin m → Fin n) (a : Fin m → F2) (i : Fin m) (x : Fin d → F2) :
    affineBit (fun k l => a l * L (Pi.single k 1) (j l))
      (fun l => a l * w (j l)) i x = a i * (w + L x) (j i) := by
  have hexpand : ∑ k, x k • (Pi.single k (1 : F2)) = x := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply, mul_ite]
  have hL : L x (j i) = ∑ k, x k * L (Pi.single k 1) (j i) := by
    simpa only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using
      congrArg (fun z => L z (j i)) hexpand.symm
  simp only [affineBit, dotProduct, Pi.add_apply, hL,
    mul_add, Finset.mul_sum]
  rw [add_comm (a i * w (j i))]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  change a i * L (Pi.single k 1) (j i) * x k = a i * (x k * L (Pi.single k 1) (j i))
  ring

private theorem exists_pointWeight_on_slice {n : ℕ} (s : ℕ)
    (M : Matrix (Fin n) (Fin n) F2) (hdiag : ∀ i, M i i = 0)
    (hsymm : ∀ i j, M i j = M j i)
    (L : (Fin (2 * (2 ^ s - 1)) → F2) →ₗ[F2] (Fin n → F2))
    (w : Fin n → F2)
    (hnd : Function.Injective ((Matrix.toBilin' M).comp L L).flip)
    (r : ZMod (2 ^ s)) :
    ∃ x, (pointWeight M (w + L x) : ZMod (2 ^ s)) = r := by
  let e : Fin (n * n) ≃ Fin n × Fin n := finProdFinEquiv.symm
  let i (k : Fin (n * n)) := (e k).1
  let j (k : Fin (n * n)) := (e k).2
  let a (k : Fin (n * n)) := strictUpper M (i k) (j k)
  let A : Matrix (Fin (2 * (2 ^ s - 1))) (Fin (n * n)) F2 :=
    fun k l => a l * L (Pi.single k 1) (i l)
  let c (l : Fin (n * n)) := a l * w (i l)
  let B : Matrix (Fin (2 * (2 ^ s - 1))) (Fin (n * n)) F2 :=
    fun k l => L (Pi.single k 1) (j l)
  let f (l : Fin (n * n)) := w (j l)
  have hA x l : affineBit A c l x = a l * (w + L x) (i l) :=
    affineBit_of_linearMap L w i a l x
  have hB x l : affineBit B f l x = (w + L x) (j l) := by
    simpa [B, f] using affineBit_of_linearMap L w j (fun _ => 1) l x
  have hweight x : quadraticAffineWeight A B c f x = pointWeight M (w + L x) := by
    unfold quadraticAffineWeight bilinearWeight
    simp only [pairBit, hA, hB]
    exact
      (Fintype.sum_equiv e (fun k => (a k * (w + L x) (i k) * (w + L x) (j k)).val)
        (fun p => (strictUpper M p.1 p.2 * (w + L x) p.1 * (w + L x) p.2).val)
        (fun _ => rfl)).trans
      (Fintype.sum_prod_type' fun i j => (strictUpper M i j * (w + L x) i * (w + L x) j).val)
  have hpolar (x y : Fin (2 * (2 ^ s - 1)) → F2) :
      (quadraticAffineWeight A B c f (x + y) : F2) +
        (quadraticAffineWeight A B c f x : F2) +
        (quadraticAffineWeight A B c f y : F2) +
        (quadraticAffineWeight A B c f 0 : F2) =
      ((Matrix.toBilin' M).comp L L) x y := by
    simp only [hweight, cast_pointWeight]
    change affinePolar (fun u => upperQuadratic M (w + L u)) x y = _
    rw [affinePolar_translate_quadratic, ← QuadraticMap.polarBilin_apply_apply,
      polarBilin_upperQuadratic M hdiag hsymm]
    rfl
  have hodd := quadraticAffineWeight_residueFibres_odd s _ _ rfl A B c f _ hpolar hnd r
  have hpos := hodd.pos
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
  exact ⟨x, by simpa [hweight] using hx⟩

/-- One colouring of the nonzero vectors meets every colour in each
nondegenerate subspace of dimension twice the number of colours. The
ambient alternating form can be degenerate. -/
theorem exists_symplecticNonzeroPointColouring
    {V : Type*} [AddCommGroup V] [Module F2 V] [FiniteDimensional F2 V]
    (β : LinearMap.BilinForm F2 V) (hAlt : β.IsAlt) (s : ℕ) (hs : 0 < s) :
    ∃ colour : {v : V // v ≠ 0} → ZMod (2 ^ s),
      ∀ (S : Submodule F2 V), (β.restrict S).Nondegenerate →
        finrank F2 S = 2 * 2 ^ s →
        ∀ r : ZMod (2 ^ s), ∃ v : {v : V // v ≠ 0}, v.val ∈ S ∧ colour v = r := by
  classical
  let e := (Module.finBasis F2 V).equivFun
  let M := (BilinForm.congr e β).toMatrix'
  have hmat (x y) : Matrix.toBilin' M x y = β (e.symm x) (e.symm y) := by
    simp [M]
  have hentry i j : M i j = β (e.symm (Pi.single i 1)) (e.symm (Pi.single j 1)) :=
    (Matrix.toBilin'_single M i j).symm.trans (hmat _ _)
  have hdiag i : M i i = 0 := (hentry i i).trans (hAlt _)
  have hsymm i j : M i j = M j i := by
    rw [hentry i j, hentry j i]
    simpa only [CharTwo.neg_eq] using
      hAlt.neg_eq (e.symm (Pi.single i 1)) (e.symm (Pi.single j 1))
  refine ⟨fun v => (pointWeight M (e v.val) : ZMod (2 ^ s)), ?_⟩
  intro S hS hSrank r
  have hq : 1 < 2 ^ s := one_lt_pow' (by decide : 1 < (2 : ℕ)) hs.ne'
  have hpos : 0 < finrank F2 S := by omega
  obtain ⟨w, W, _, hwW, hW, hWrank⟩ :=
    exists_nondegenerate_codimTwo_slice (β.restrict S) (fun v => hAlt v) hS hpos
  have hWr : finrank F2 W = 2 * (2 ^ s - 1) := by omega
  let u := (Module.finBasisOfFinrankEq F2 W hWr).equivFun.symm
  let inclusion : W →ₗ[F2] V := S.subtype.comp W.subtype
  let L := e.toLinearMap.comp (inclusion.comp u.toLinearMap)
  let b := (Matrix.toBilin' M).comp L L
  have hb : b = BilinForm.congr u.symm ((β.restrict S).restrict W) := by
    apply LinearMap.ext₂
    intro x y
    change Matrix.toBilin' M (e (inclusion (u x))) (e (inclusion (u y))) = _
    rw [hmat]
    simp only [LinearEquiv.symm_apply_apply, BilinForm.congr_apply,
      LinearEquiv.symm_symm]
    rfl
  have hinj : Function.Injective b.flip := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.separatingRight_iff_flip_ker_eq_bot.mp
    rw [hb]
    exact (hW.congr u.symm).2
  obtain ⟨x, hx⟩ := exists_pointWeight_on_slice s M hdiag hsymm L (e w.val) hinj r
  let v : S := w + (u x).val
  have hv0 : v ≠ 0 := by
    intro hv
    apply hwW
    have heq : w = -(u x).val := eq_neg_of_add_eq_zero_left hv
    rw [heq]
    exact W.neg_mem (u x).property
  refine ⟨⟨v.val, fun hv => hv0 (Subtype.ext hv)⟩, v.property, ?_⟩
  change (pointWeight M (e v.val) : ZMod (2 ^ s)) = r
  have hcoords : e v.val = e w.val + L x := by
    change e (w.val + (inclusion (u x))) = _
    rw [map_add]
    rfl
  exact hcoords.symm ▸ hx

private theorem exists_unique_nonzero_mem_of_finrank_one
    {V : Type*} [AddCommGroup V] [Module F2 V]
    (P : Submodule F2 V) (hP : finrank F2 P = 1) :
    ∃! v : {v : V // v ≠ 0}, v.val ∈ P := by
  obtain ⟨v, hv0, hspan⟩ := (finrank_eq_one_iff' (K := F2) (V := ↥P)).mp hP
  refine ⟨⟨v.val, fun hv => hv0 (Subtype.ext hv)⟩, v.property, ?_⟩
  intro w hw
  obtain ⟨a, ha⟩ := hspan ⟨w.val, hw⟩
  rcases f2_eq_zero_or_one a with h | h
  · exact (w.property (by simpa [h] using (congrArg Subtype.val ha).symm)).elim
  · apply Subtype.ext
    simpa [h] using (congrArg Subtype.val ha).symm

/-- The persistent colouring in the circulation proof. Each nondegenerate
subspace of dimension `2 * 2 ^ s` contains a one-dimensional subspace of
every colour, for a single choice of colouring of the ambient lines. -/
theorem exists_symplecticPointColouring
    {V : Type*} [AddCommGroup V] [Module F2 V] [FiniteDimensional F2 V]
    (β : LinearMap.BilinForm F2 V) (hAlt : β.IsAlt) (s : ℕ) (hs : 0 < s) :
    ∃ colour : {P : Submodule F2 V // finrank F2 P = 1} → ZMod (2 ^ s),
      ∀ (S : Submodule F2 V), (β.restrict S).Nondegenerate →
        finrank F2 S = 2 * 2 ^ s →
        ∀ r : ZMod (2 ^ s), ∃ P : {P : Submodule F2 V // finrank F2 P = 1},
          P.val ≤ S ∧ colour P = r := by
  classical
  obtain ⟨colour, hcolour⟩ := exists_symplecticNonzeroPointColouring β hAlt s hs
  let point (P : {P : Submodule F2 V // finrank F2 P = 1}) :=
    (exists_unique_nonzero_mem_of_finrank_one P.val P.property).exists.choose
  refine ⟨fun P => colour (point P), ?_⟩
  intro S hS hdim r
  obtain ⟨v, hv, hcol⟩ := hcolour S hS hdim r
  let P : {P : Submodule F2 V // finrank F2 P = 1} :=
    ⟨F2 ∙ v.val, finrank_span_singleton v.property⟩
  refine ⟨P, (span_singleton_le_iff_mem v.val S).mpr hv, ?_⟩
  have hpoint : point P = v :=
    (exists_unique_nonzero_mem_of_finrank_one P.val P.property).unique
      (exists_unique_nonzero_mem_of_finrank_one P.val P.property).exists.choose_spec
      (Submodule.mem_span_singleton_self v.val)
  simpa only [hpoint] using hcol

end SuccessorTree.NonPrecompact
