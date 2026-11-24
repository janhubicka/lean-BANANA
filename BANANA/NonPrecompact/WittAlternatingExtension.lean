import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Prescribed pairings for one-point extensions

To perform a one-point extension, realise the desired pairings inside a
finite nondegenerate stage, then add a fresh vector orthogonal to that
stage. The subspace on which the pairings are prescribed can be degenerate.
In an infinite-dimensional nondegenerate space, the kernel of the pairing
map also provides fresh vectors outside any finite-dimensional subspace.
-/

namespace SuccessorTree.NonPrecompact

/-- Any functional on a subspace of a finite nondegenerate stage is
represented by pairing with a vector in that stage. -/
theorem exists_wittStage_pairing
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) (U W : Submodule K V)
    [FiniteDimensional K W] (hUW : U ≤ W)
    (hW : (B.restrict W).Nondegenerate) (l : Module.Dual K U) :
    ∃ w : W, ∀ u : U, B w u = l u := by
  obtain ⟨l', hl'⟩ := LinearMap.dualMap_surjective_of_injective
    (Submodule.inclusion_injective hUW) l
  refine ⟨((B.restrict W).toDual hW).symm l', fun u => ?_⟩
  exact (LinearMap.BilinForm.apply_toDual_symm_apply (hB := hW) l'
      (U.inclusion hUW u)).trans (DFunLike.congr_fun hl' u)

/-- Adding a fresh orthogonal vector realises the pairings of the new
point without placing it in the old stage. -/
theorem exists_wittExtension_pairing
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) (U W : Submodule K V)
    [FiniteDimensional K W] (hUW : U ≤ W)
    (hW : (B.restrict W).Nondegenerate) (l : Module.Dual K U)
    (e : V) (he : e ∉ W) (horth : ∀ w : W, B e w = 0) :
    ∃ v : V, v ∉ W ∧ ∀ u : U, B v u = l u := by
  obtain ⟨w, hw⟩ := exists_wittStage_pairing B U W hUW hW l
  refine ⟨(w : V) + e, ?_, fun u => ?_⟩
  · intro h
    exact he (by simpa using W.sub_mem h w.property)
  · have hu : B e (u : V) = 0 := horth ⟨u, hUW u.property⟩
    rw [map_add, LinearMap.add_apply, hw, hu, add_zero]

/-- In an infinite-dimensional nondegenerate space, prescribed pairings on
a finite-dimensional subspace can be realised outside any finite-dimensional
subspace. -/
theorem exists_witt_pairing_outside
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)
    (hinf : ¬ FiniteDimensional K V)
    (U W : Submodule K V) [FiniteDimensional K U] [FiniteDimensional K W]
    (l : Module.Dual K U) : ∃ v : V, v ∉ W ∧ ∀ u : U, B v u = l u := by
  classical
  let f : V →ₗ[K] Module.Dual K U := U.dualRestrict.comp B
  have hflip : Function.Injective f.flip := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro u hu
    apply Subtype.ext
    apply hB.2
    intro v
    exact DFunLike.congr_fun hu v
  obtain ⟨x, hx⟩ := LinearMap.flip_injective_iff₂.mp hflip l
  by_cases hxW : x ∈ W
  · have hker : ¬ f.ker ≤ W := by
      intro h
      let _ : FiniteDimensional K f.ker :=
        FiniteDimensional.of_injective (Submodule.inclusion h) (Submodule.inclusion_injective h)
      have htop : FiniteDimensional K ((⊤ : Submodule K (Module.Dual K U)).comap f) :=
        inferInstance
      rw [Submodule.comap_top] at htop
      exact hinf (FiniteDimensional.of_surjective (⊤ : Submodule K V).subtype
        (fun v => ⟨⟨v, Submodule.mem_top⟩, rfl⟩))
    obtain ⟨e, he, heW⟩ := Set.not_subset.mp hker
    refine ⟨x + e, fun h => heW (by simpa using W.sub_mem h hxW), fun u => ?_⟩
    have hxe : f (x + e) = l := by rw [map_add, hx, LinearMap.mem_ker.mp he, add_zero]
    exact DFunLike.congr_fun hxe u
  · exact ⟨x, hxW, fun u => DFunLike.congr_fun hx u⟩

end SuccessorTree.NonPrecompact
