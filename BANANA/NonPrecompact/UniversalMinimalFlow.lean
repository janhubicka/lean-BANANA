import Mathlib.Dynamics.Minimal
import Mathlib.GroupTheory.GroupAction.SubMulAction
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.ExtremallyDisconnected
import Mathlib.Topology.Sequences
import Mathlib.Topology.Metrizable.Basic

/-!
# Minimal compact flows and compact images in extremally disconnected spaces
-/

namespace SuccessorTree.NonPrecompact

open Set Filter Function Topology MulAction
open scoped Pointwise

universe u v w

/-- Every nonempty compact Hausdorff flow has a nonempty minimal closed subflow. -/
theorem exists_minimal_closed_subflow (G : Type u) (X : Type v)
    [Group G] [TopologicalSpace G] [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [Nonempty X] [MulAction G X] [ContinuousSMul G X] :
    ∃ (Y : Set X), IsClosed Y ∧ Y.Nonempty ∧ (∀ g : G, g • Y ⊆ Y) ∧
      ∀ y ∈ Y, closure (orbit G y) = Y := by
  let candidates : Set (Set X) :=
    {Y | IsClosed Y ∧ Y.Nonempty ∧ ∀ g : G, g • Y ⊆ Y}
  have hu : (univ : Set X) ∈ candidates :=
    ⟨isClosed_univ, univ_nonempty, fun _ => subset_univ _⟩
  obtain ⟨Y, hY⟩ := zorn_superset candidates (by
    intro C hC hchain
    by_cases h : Nonempty C
    · letI := h
      let Z := ⋂ c : C, c.val
      have hc (c : C) : c.val ∈ candidates := hC c.property
      refine ⟨Z, ⟨isClosed_iInter fun c => (hc c).1, ?_, ?_⟩,
        fun c hc _ hx => mem_iInter.mp hx ⟨c, hc⟩⟩
      · refine IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
          (fun c : C => c.val) ?_ (fun c => (hc c).2.1)
          (fun c => (hc c).1.isCompact) (fun c => (hc c).1)
        intro a b
        by_cases hab : a.val = b.val
        · exact ⟨a, subset_rfl, by change a.val ⊆ b.val; rw [hab]⟩
        · rcases hchain a.property b.property hab with h | h
          · exact ⟨a, subset_rfl, h⟩
          · exact ⟨b, h, subset_rfl⟩
      · rintro g _ ⟨x, hx, rfl⟩
        exact mem_iInter.mpr fun c => (hc c).2.2 g ⟨x, mem_iInter.mp hx c, rfl⟩
    · refine ⟨univ, hu, fun c hc => ?_⟩
      exact (h ⟨⟨c, hc⟩⟩).elim)
  obtain ⟨hclosed, hne, hInv⟩ := hY.prop
  refine ⟨Y, hclosed, hne, hInv, fun y hy => ?_⟩
  apply hY.eq_of_subset
  · exact ⟨isClosed_closure, (nonempty_orbit _).closure, fun g => smul_closure_orbit_subset g y⟩
  · exact closure_minimal (by rintro _ ⟨g, rfl⟩; exact hInv g ⟨y, hy, rfl⟩) hclosed

/-- A nonempty compact Hausdorff flow has a compact, nonempty minimal subaction. -/
theorem exists_compact_minimal_subaction (G : Type u) (X : Type v)
    [Group G] [TopologicalSpace G] [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [Nonempty X] [MulAction G X] [ContinuousSMul G X] :
    ∃ Y : SubMulAction G X, CompactSpace Y ∧ Nonempty Y ∧
      ContinuousSMul G Y ∧ IsMinimal G Y := by
  obtain ⟨Y, hclosed, hne, hinv, hminimal⟩ := exists_minimal_closed_subflow G X
  let S : SubMulAction G X := ⟨Y, fun g x hx => hinv g ⟨x, hx, rfl⟩⟩
  refine ⟨S, isCompact_iff_compactSpace.mp hclosed.isCompact, hne.coe_sort, ?_, ?_⟩
  · exact ⟨(continuous_fst.smul (continuous_subtype_val.comp continuous_snd)).subtype_mk _⟩
  · refine ⟨fun x => ?_⟩
    rw [dense_iff_closure_eq]
    ext z
    rw [closure_subtype, SubMulAction.val_image_orbit, hminimal x.val x.property]
    exact iff_of_true z.property (mem_univ z)

/-- The universal mapping property among nonempty compact Hausdorff minimal flows. -/
def UniversalAmongMinimalFlows (G : Type u) (M : Type v)
    [Group G] [TopologicalSpace G] [TopologicalSpace M] [MulAction G M] : Prop :=
  ∀ (Y : Type w) [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [Nonempty Y]
    [MulAction G Y] [ContinuousSMul G Y] [MulAction.IsMinimal G Y],
    ∃ f : M → Y, Continuous f ∧ Surjective f ∧ ∀ (g : G) (x : M), f (g • x) = g • f x

/-- An injective sequence cannot converge in a Hausdorff extremally disconnected space. -/
theorem not_injective_tendsto_of_extremallyDisconnected {X : Type*}
    [TopologicalSpace X] [T2Space X] [ExtremallyDisconnected X] {f : ℕ → X} {x : X}
    (hf : Tendsto f atTop (𝓝 x)) : ¬ Injective f := by
  classical
  intro hi
  have hne : ∀ᶠ n in atTop, f n ≠ x := by
    by_cases hr : x ∈ range f
    · obtain ⟨m, hm⟩ := hr
      filter_upwards [eventually_gt_atTop m] with n hn hp
      exact hn.ne' (hi (hp.trans hm.symm))
    · exact Eventually.of_forall fun n h => hr ⟨n, h⟩
  let P (U : Set X) : Prop :=
    (∃ n : ℕ, f n ∈ U) ∧ IsOpen U ∧ Uᶜ ∈ 𝓝 x
  letI : Std.Symm (α := Set X) Disjoint := ⟨fun _ _ h => h.symm⟩
  obtain ⟨U, hU, hDisj⟩ :=
    exists_seq_of_forall_finset_exists' P Disjoint (by
      intro S hS
      let C := ⋂ U ∈ S, interior (Uᶜ)
      have hC : C ∈ 𝓝 x := (biInter_finset_mem _).2
        fun U hU => interior_mem_nhds.2 (hS U hU).2.2
      obtain ⟨n, hnx, hnC⟩ := (hne.and (hf.eventually_mem hC)).exists
      obtain ⟨V, W, hVo, hWo, hnV, hxW, hVW⟩ := t2_separation hnx
      refine ⟨V ∩ C, ⟨⟨n, hnV, hnC⟩,
        hVo.inter (isOpen_biInter_finset fun _ _ => isOpen_interior), ?_⟩, ?_⟩
      · exact mem_of_superset (hWo.mem_nhds hxW)
          fun _ hz hzV => disjoint_left.1 hVW hzV.1 hz
      · intro U hU
        exact disjoint_left.2 fun _ hzU hzV =>
          interior_subset (mem_iInter₂.1 hzV.2 U hU) hzU)
  choose a ha using fun n => (hU n).1
  have haInj : Injective a := by
    intro i j hij
    by_contra hne'
    exact disjoint_left.1 (hDisj hne') (ha i) (hij ▸ ha j)
  let V := ⋃ n : ℕ, U (2 * n)
  let W := ⋃ n : ℕ, U (2 * n + 1)
  have hVW : Disjoint V W := by
    apply disjoint_iUnion_left.2
    intro i
    apply disjoint_iUnion_right.2
    intro j
    exact hDisj (by omega)
  have hV : x ∈ closure V :=
    mem_closure_of_tendsto (hf.comp (haInj.comp (by
      intro i j h
      dsimp at h
      omega : Injective (fun n : ℕ => 2 * n))).nat_tendsto_atTop)
      (Eventually.of_forall fun n => mem_iUnion.2 ⟨n, ha (2 * n)⟩)
  have hW : x ∈ closure W :=
    mem_closure_of_tendsto (hf.comp (haInj.comp (by
      intro i j h
      dsimp at h
      omega : Injective (fun n : ℕ => 2 * n + 1))).nat_tendsto_atTop)
      (Eventually.of_forall fun n => mem_iUnion.2 ⟨n, ha (2 * n + 1)⟩)
  exact disjoint_left.1 (ExtremallyDisconnected.disjoint_closure_of_disjoint_isOpen hVW
    (isOpen_iUnion fun n => (hU (2 * n)).2.1)
    (isOpen_iUnion fun n => (hU (2 * n + 1)).2.1)) hV hW

/-- Every continuous image of a sequentially compact space in a Hausdorff
extremally disconnected space is finite. -/
theorem finite_range_of_seqCompact_extremallyDisconnected {M X : Type*}
    [TopologicalSpace M] [SeqCompactSpace M] [TopologicalSpace X] [T2Space X]
    [ExtremallyDisconnected X] {f : M → X} (hf : Continuous f) :
    (range f).Finite := by
  by_contra h
  letI : Infinite (range f) := infinite_coe_iff.mpr h
  let e := Infinite.natEmbedding (range f)
  let s (n : ℕ) : X := (e n).val
  obtain ⟨x, _, φ, hφ, hlim⟩ := (IsSeqCompact.range hf.seqContinuous) (fun n => (e n).property)
  exact not_injective_tendsto_of_extremallyDisconnected hlim
    ((Subtype.val_injective.comp e.injective).comp hφ.injective)

end SuccessorTree.NonPrecompact
