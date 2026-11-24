import BANANA.NonPrecompact.WittAlternatingExtension
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Span.Basic

/-!
# Adjoining a vector to a partial isometry

Extending a partial isometry by one vector only requires preserving its
pairings against the old domain. The two new self-pairings vanish for
alternating forms.
-/

namespace SuccessorTree.NonPrecompact

/-- A linear isometric injection on a subspace extends to the span of that
subspace and one vector when its prescribed image lies outside the old range
and has the required pairings. -/
theorem exists_wittAdjoinIsometry
    {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]
    (B : LinearMap.BilinForm K V) (C : LinearMap.BilinForm K W)
    (hB : B.IsAlt) (hC : C.IsAlt) (S : Submodule K V)
    (f : S →ₗ[K] W) (hf : Function.Injective f)
    (hiso : ∀ u v : S, C (f u) (f v) = B u v)
    (x : V) (hx : x ∉ S) (y : W) (hy : y ∉ LinearMap.range f)
    (hpair : ∀ u : S, C y (f u) = B x u) :
    ∃ F : (S ⊔ K ∙ x : Submodule K V) →ₗ[K] W,
      Function.Injective F ∧
      (∀ u v, C (F u) (F v) = B u v) ∧
      (∀ u : S, F (S.inclusion le_sup_left u) = f u) ∧
      F ⟨x, Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)⟩ = y := by
  classical
  let a : S × K →ₗ[K] V := S.subtype.coprod (LinearMap.toSpanSingleton K V x)
  let b : S × K →ₗ[K] W := f.coprod (LinearMap.toSpanSingleton K W y)
  have hx0 : x ≠ 0 := fun h => hx (h.symm ▸ S.zero_mem)
  have hy0 : y ≠ 0 := fun h => hy (h.symm ▸ (LinearMap.range f).zero_mem)
  have ha : LinearMap.range a = S ⊔ K ∙ x := by
    dsimp only [a]
    rw [LinearMap.range_coprod, Submodule.range_subtype, LinearMap.range_toSpanSingleton]
  have hai : Function.Injective a := by
    apply LinearMap.ker_eq_bot.mp
    dsimp only [a]
    rw [LinearMap.ker_coprod_of_disjoint_range, Submodule.ker_subtype,
      LinearMap.ker_toSpanSingleton K hx0]
    · simp
    · rw [Submodule.range_subtype, LinearMap.range_toSpanSingleton]
      exact Submodule.disjoint_span_singleton_of_notMem hx
  have hbi : Function.Injective b := by
    apply LinearMap.ker_eq_bot.mp
    dsimp only [b]
    rw [LinearMap.ker_coprod_of_disjoint_range, LinearMap.ker_eq_bot.mpr hf,
      LinearMap.ker_toSpanSingleton K hy0]
    · simp
    · rw [LinearMap.range_toSpanSingleton]
      exact Submodule.disjoint_span_singleton_of_notMem hy
  let e : (S × K) ≃ₗ[K] (S ⊔ K ∙ x : Submodule K V) :=
    (LinearEquiv.ofInjective a hai).trans (LinearEquiv.ofEq _ _ ha)
  have hea (u : S × K) : (e u : V) = a u := rfl
  have heb (u : S × K) : b u = f u.1 + u.2 • y := rfl
  refine ⟨b.comp e.symm.toLinearMap, hbi.comp e.symm.injective, ?_, ?_, ?_⟩
  · intro u v
    obtain ⟨⟨u, r⟩, rfl⟩ := e.surjective u
    obtain ⟨⟨v, s⟩, rfl⟩ := e.surjective v
    have hpair' : C (f u) y = B u x := by
      rw [← hC.neg_eq y (f u), hpair u, hB.neg_eq x u]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      hea, heb, a, LinearMap.coprod_apply, Submodule.coe_subtype,
      LinearMap.toSpanSingleton_apply, LinearMap.BilinForm.add_left,
      LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_left,
      LinearMap.BilinForm.smul_right, hiso, hpair, hpair', hB.self_eq_zero, hC.self_eq_zero]
  · intro u
    have h : e (u, 0) = S.inclusion le_sup_left u := by
      apply Subtype.ext
      simp [hea, a, LinearMap.coprod_apply]
    rw [← h]
    simp [heb]
  · have h : e (0, 1) = ⟨x, Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)⟩ := by
      apply Subtype.ext
      simp [hea, a, LinearMap.coprod_apply]
    rw [← h]
    simp [heb]

/-- Every finite-dimensional partial isometry into an infinite-dimensional
nondegenerate alternating space extends by one vector. -/
theorem exists_wittOnePointIsometry
    {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]
    (B : LinearMap.BilinForm K V) (C : LinearMap.BilinForm K W)
    (hB : B.IsAlt) (hC : C.IsAlt) (hC_nonDeg : C.Nondegenerate)
    (hinf : ¬ FiniteDimensional K W) (S : Submodule K V) [FiniteDimensional K S]
    (f : S →ₗ[K] W) (hf : Function.Injective f)
    (hiso : ∀ u v : S, C (f u) (f v) = B u v)
    (x : V) (hx : x ∉ S) :
    ∃ F : (S ⊔ K ∙ x : Submodule K V) →ₗ[K] W,
      Function.Injective F ∧ (∀ u v, C (F u) (F v) = B u v) ∧
      ∀ u : S, F (S.inclusion le_sup_left u) = f u := by
  let e := LinearEquiv.ofInjective f hf
  let l : Module.Dual K (LinearMap.range f) := (B x).comp (S.subtype.comp e.symm.toLinearMap)
  obtain ⟨y, hy, hpair⟩ := exists_witt_pairing_outside C hC_nonDeg hinf f.range f.range l
  have hpair' (u : S) : C y (f u) = B x u := by
    calc
      C y (f u) = l (e u) := hpair (e u)
      _ = B x u := by simp [l]
  obtain ⟨F, hF, hFiso, hFextends, _⟩ :=
    exists_wittAdjoinIsometry B C hB hC S f hf hiso x hx y hy hpair'
  exact ⟨F, hF, hFiso, hFextends⟩

end SuccessorTree.NonPrecompact
