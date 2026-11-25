import BANANA.NonPrecompact.BananaLimitFirstOrder
import BANANA.NonPrecompact.FirstOrderOrbitExpansion
import Mathlib.Algebra.Module.ZMod
import Mathlib.Data.Fin.VecNotation
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# The pointwise group of the tagged BANANA presentation

A first-order automorphism preserves each tag and the two addition
graphs, so its two restrictions are linear equivalences over the
two-element field. Preservation of the edge relation determines
preservation of the pairing. The native and encoded topologies agree
because both use agreement on finite tuples of tagged points.
-/

namespace SuccessorTree.NonPrecompact

open Filter FirstOrder Set Topology
open scoped FirstOrder

private abbrev TaggedAut := FirstOrderAut bananaTaggedLanguage BananaTaggedCarrier

private def component (g : TaggedAut) (tag : BananaLimitVector → BananaTaggedCarrier)
    (x : BananaLimitVector) : BananaLimitVector :=
  Sum.elim id id (g.toEquiv (tag x))

private theorem map_leftTag (g : TaggedAut) (x : BananaLimitVector) :
    g.toEquiv (.inl x) = .inl (component g Sum.inl x) := by
  have h := (g.toEquiv.map_rel BananaTaggedRelation.left (fun _ => Sum.inl x)).mpr trivial
  change (match g.toEquiv (.inl x) with | .inl _ => True | .inr _ => False) at h
  cases hg : g.toEquiv (.inl x) with
  | inl y => simp only [component, hg, Sum.elim_inl, id_eq]
  | inr y => simp only [hg] at h

private theorem map_rightTag (g : TaggedAut) (x : BananaLimitVector) :
    g.toEquiv (.inr x) = .inr (component g Sum.inr x) := by
  have h := (g.toEquiv.map_rel BananaTaggedRelation.right (fun _ => Sum.inr x)).mpr trivial
  change (match g.toEquiv (.inr x) with | .inl _ => False | .inr _ => True) at h
  cases hg : g.toEquiv (.inr x) with
  | inl y => simp only [hg] at h
  | inr y => simp only [component, hg, Sum.elim_inr, id_eq]

private theorem map_leftAdd (g : TaggedAut) (x y : BananaLimitVector) :
    component g Sum.inl (x + y) = component g Sum.inl x + component g Sum.inl y := by
  have h := (g.toEquiv.map_rel BananaTaggedRelation.leftAdd
    ![Sum.inl x, Sum.inl y, Sum.inl (x + y)]).mpr rfl
  change bananaTaggedStructure.RelMap BananaTaggedRelation.leftAdd
    ![g.toEquiv (.inl x), g.toEquiv (.inl y), g.toEquiv (.inl (x + y))] at h
  rw [map_leftTag, map_leftTag, map_leftTag] at h
  exact h.symm

private theorem map_rightAdd (g : TaggedAut) (x y : BananaLimitVector) :
    component g Sum.inr (x + y) = component g Sum.inr x + component g Sum.inr y := by
  have h := (g.toEquiv.map_rel BananaTaggedRelation.rightAdd
    ![Sum.inr x, Sum.inr y, Sum.inr (x + y)]).mpr rfl
  change bananaTaggedStructure.RelMap BananaTaggedRelation.rightAdd
    ![g.toEquiv (.inr x), g.toEquiv (.inr y), g.toEquiv (.inr (x + y))] at h
  rw [map_rightTag, map_rightTag, map_rightTag] at h
  exact h.symm

private def componentLinearEquiv
    (tag : BananaLimitVector → BananaTaggedCarrier)
    (hproj : ∀ x, Sum.elim id id (tag x) = x)
    (htag : ∀ (g : TaggedAut) x, g.toEquiv (tag x) = tag (component g tag x))
    (hadd : ∀ (g : TaggedAut) x y, component g tag (x + y) =
      component g tag x + component g tag y)
    (g : TaggedAut) : BananaLimitVector ≃ₗ[F2] BananaLimitVector where
  toFun := component g tag
  invFun := component g⁻¹ tag
  left_inv x := by
    change Sum.elim id id (g.toEquiv.symm (tag (component g tag x))) = x
    rw [← htag, g.toEquiv.symm_apply_apply, hproj]
  right_inv x := by
    change Sum.elim id id (g.toEquiv (tag (component g⁻¹ tag x))) = x
    rw [← htag (g⁻¹)]
    change Sum.elim id id (g.toEquiv (g.toEquiv.symm (tag x))) = x
    rw [g.toEquiv.apply_symm_apply, hproj]
  map_add' := hadd g
  map_smul' := fun c x => ZMod.map_smul (AddMonoidHom.mk' (component g tag) (hadd g)) c x

/-- Forgetting the tags of the two restrictions recovers the
native pairing-preserving linear automorphism. -/
def bananaLimit_nativeAut (g : FirstOrderAut bananaTaggedLanguage BananaTaggedCarrier) :
    BananaLimitAutomorphism :=
  ⟨(componentLinearEquiv Sum.inl (fun _ => rfl) map_leftTag map_leftAdd g,
    componentLinearEquiv Sum.inr (fun _ => rfl) map_rightTag map_rightAdd g),
    fun x y => by
      change bananaLimitPairing (component g Sum.inl x) (component g Sum.inr y) =
        bananaLimitPairing x y
      have h := g.toEquiv.map_rel BananaTaggedRelation.edge ![Sum.inl x, Sum.inr y]
      change bananaTaggedStructure.RelMap BananaTaggedRelation.edge
        ![g.toEquiv (.inl x), g.toEquiv (.inr y)] ↔ bananaLimitPairing x y = 1 at h
      rw [map_leftTag, map_rightTag] at h
      change bananaLimitPairing (component g Sum.inl x) (component g Sum.inr y) = 1 ↔
        bananaLimitPairing x y = 1 at h
      rcases f2_eq_zero_or_one (bananaLimitPairing x y) with h0 | h1
      · exact ((f2_eq_zero_or_one _).resolve_right (by simpa [h0] using h)).trans h0.symm
      · exact (h.mpr h1).trans h1.symm⟩

/-- The reverse identification acts identically on every tagged point. -/
theorem bananaLimit_nativeAut_smul
    (g : FirstOrderAut bananaTaggedLanguage BananaTaggedCarrier) (a : BananaTaggedCarrier) :
    bananaLimit_nativeAut g • a = g.toEquiv a := by
  cases a with
  | inl x => exact (map_leftTag g x).symm
  | inr y => exact (map_rightTag g y).symm

private theorem continuous_firstOrderAut :
    Continuous bananaLimit_firstOrderAut := by
  rw [continuous_iff_continuousAt]
  intro g U hU
  obtain ⟨n, a, ha⟩ :=
    FirstOrderAut.exists_tupleEval_subset_of_mem_nhds (bananaLimit_firstOrderAut g) U hU
  change bananaLimit_firstOrderAut ⁻¹' U ∈ 𝓝 g
  have h := (isOpen_bananaLimitTaggedTupleEval a (g • a)).mem_nhds
    (show g ∈ {f : BananaLimitAutomorphism | f • a = g • a} from rfl)
  exact mem_of_superset h fun f hf => ha fun i => by
    simpa only [bananaLimit_firstOrderAut_apply, Pi.smul_apply] using congrFun hf i

private theorem continuous_nativeAut :
    Continuous bananaLimit_nativeAut := by
  rw [continuous_iff_continuousAt]
  intro g U hU
  obtain ⟨n, a, ha⟩ :=
    exists_bananaLimitTaggedTupleEval_subset_of_mem_nhds (bananaLimit_nativeAut g) U hU
  change bananaLimit_nativeAut ⁻¹' U ∈ 𝓝 g
  have h := (FirstOrderAut.isOpen_tupleEval a (g.toEquiv ∘ a)).mem_nhds
    (show g ∈ {f : TaggedAut | ∀ i, f.toEquiv (a i) = (g.toEquiv ∘ a) i} from fun _ => rfl)
  exact mem_of_superset h fun f hf => ha (funext fun i => by
    simpa only [Pi.smul_apply, bananaLimit_nativeAut_smul, Function.comp_apply] using hf i)

/-- The native and first-order automorphism groups of the BANANA limit
are continuously isomorphic for their pointwise topologies. -/
noncomputable def bananaLimit_firstOrderAutIso :
    BananaLimitAutomorphism ≃ₜ* FirstOrderAut bananaTaggedLanguage BananaTaggedCarrier where
  toFun := bananaLimit_firstOrderAut
  invFun := bananaLimit_nativeAut
  left_inv g := by
    apply Subtype.ext
    apply Prod.ext
    · apply LinearEquiv.ext
      intro x
      exact Sum.inl.inj (bananaLimit_nativeAut_smul (bananaLimit_firstOrderAut g) (.inl x))
    · apply LinearEquiv.ext
      intro x
      exact Sum.inr.inj (bananaLimit_nativeAut_smul (bananaLimit_firstOrderAut g) (.inr x))
  right_inv g := by
    apply FirstOrder.Language.Equiv.ext
    intro a
    change (bananaLimit_firstOrderAut (bananaLimit_nativeAut g)).toEquiv a = g.toEquiv a
    rw [bananaLimit_firstOrderAut_apply]
    exact bananaLimit_nativeAut_smul g a
  map_mul' g h := by
    apply FirstOrder.Language.Equiv.ext
    intro x
    cases x <;> rfl
  continuous_toFun := continuous_firstOrderAut
  continuous_invFun := continuous_nativeAut

/-- The isomorphism respects the common action on tagged points. -/
theorem bananaLimit_firstOrderAutIso_apply
    (g : BananaLimitAutomorphism) (a : BananaTaggedCarrier) :
    (bananaLimit_firstOrderAutIso g).toEquiv a = g • a :=
  bananaLimit_firstOrderAut_apply g a

/-- The finite covering property passes along a topological group
isomorphism. -/
theorem CoPrecompact.map_continuousMulEquiv
    {G K : Type*} [Group G] [Group K] [TopologicalSpace G] [TopologicalSpace K]
    {H : Subgroup G} (hH : CoPrecompact G H) (e : G ≃ₜ* K) :
    CoPrecompact K (H.map e.toMulEquiv.toMonoidHom) := by
  classical
  intro U hU
  have hU' : U ∈ 𝓝 (e 1) := by simpa only [map_one] using hU
  obtain ⟨F, hF⟩ := hH (e ⁻¹' U) ((map_continuous e).continuousAt.preimage_mem_nhds hU')
  refine ⟨F.image e, fun k => ?_⟩
  obtain ⟨f, hf, u, hu, h, heq⟩ := hF (e.symm k)
  refine ⟨e f, Finset.mem_image.mpr ⟨f, hf, rfl⟩, e u, hu,
    ⟨e h, ⟨h, h.property, rfl⟩⟩, ?_⟩
  calc
    k = e (e.symm k) := (e.apply_symm_apply k).symm
    _ = e (u * f * h) := congrArg e heq
    _ = e u * e f * e h := by simp only [map_mul]

/-- Naming the orbits of a native co-precompact subgroup gives a
countably categorical expansion of the tagged BANANA limit. -/
theorem bananaLimit_categorical_nativeOrbitExpansion
    (H : Subgroup BananaLimitAutomorphism) (hH : CoPrecompact BananaLimitAutomorphism H) :
    Cardinal.Categorical Cardinal.aleph0
      ((bananaTaggedLanguage.sum (FirstOrderAut.tupleOrbitLanguage
        (H.map bananaLimit_firstOrderAutIso.toMulEquiv.toMonoidHom))).completeTheory
        BananaTaggedCarrier) :=
  FirstOrderAut.categorical_orbitExpansion_of_coprecompact _
    (hH.map_continuousMulEquiv bananaLimit_firstOrderAutIso)
    bananaLimit_firstOrder_finite_tuple_orbit_representatives

/-- The reduct automorphism group of the orbit expansion is the image of
the native subgroup's closure in its native pointwise topology. -/
theorem bananaLimit_range_restrict_nativeOrbitExpansionAut
    (H : Subgroup BananaLimitAutomorphism) :
    Set.range (FirstOrderAut.restrictOrbitExpansionAut
      (H.map bananaLimit_firstOrderAutIso.toMulEquiv.toMonoidHom)) =
    (H.topologicalClosure.map bananaLimit_firstOrderAutIso.toMulEquiv.toMonoidHom :
      Set (FirstOrderAut bananaTaggedLanguage BananaTaggedCarrier)) := by
  rw [FirstOrderAut.range_restrictOrbitExpansionAut, Subgroup.topologicalClosure_coe,
    Subgroup.coe_map, Subgroup.coe_map, Subgroup.topologicalClosure_coe]
  exact (bananaLimit_firstOrderAutIso.toHomeomorph.image_closure _).symm

end SuccessorTree.NonPrecompact
