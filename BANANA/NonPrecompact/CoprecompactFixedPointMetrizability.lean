import BANANA.NonPrecompact.FirstOrderExtremelyAmenableDegree
import BANANA.NonPrecompact.UniversalMinimalFlow
import Mathlib.Topology.Metrizable.Urysohn

/-!
# Metrisability from co-precompactness and a fixed point

Each identity neighbourhood gives a finite closed cover of a compact flow
with a dense orbit and a point fixed by a co-precompact subgroup. Small
enough identity neighbourhoods refine any open cover. For a first-countable
group the complements of unions of pieces of these covers form a countable
basis for the flow.
-/

namespace SuccessorTree.NonPrecompact

open Filter Set Topology MulAction TopologicalSpace

universe u v

variable {G : Type u} {X : Type v} [Group G] [TopologicalSpace G]
  [TopologicalSpace X] [CompactSpace X] [T2Space X] [MulAction G X] [ContinuousSMul G X]

/-- Sufficiently small translates of each point have closure in a member of
a given open cover of a compact flow. -/
private theorem exists_closed_moves_refine_open_cover {ι : Type*} (V : ι → Set X)
    (hV : ∀ i, IsOpen (V i)) (hcover : ∀ x, ∃ i, x ∈ V i) :
    ∃ U ∈ 𝓝 (1 : G), ∀ x : X, ∃ i,
      closure ((fun g : G => g • x) '' U) ⊆ V i := by
  classical
  have hlocal (x : X) :
      ∃ (A : Set G) (B C : Set X) (i : ι),
        A ∈ 𝓝 (1 : G) ∧ B ∈ 𝓝 x ∧ IsClosed C ∧ C ⊆ V i ∧
          ∀ g ∈ A, ∀ y ∈ B, g • y ∈ C := by
    obtain ⟨i, hi⟩ := hcover x
    obtain ⟨C, hCx, hC, hCV⟩ := exists_mem_nhds_isClosed_subset ((hV i).mem_nhds hi)
    have hpre : (fun p : G × X => p.1 • p.2) ⁻¹' C ∈ 𝓝 ((1 : G), x) := by
      have hcont : Continuous (fun p : G × X => p.1 • p.2) :=
        continuous_fst.smul continuous_snd
      simpa only [one_smul] using hcont.continuousAt.preimage_mem_nhds
        (x := ((1 : G), x)) (by simpa only [one_smul] using hCx)
    obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.mp hpre
    exact ⟨A, B, C, i, hA, hB, hC, hCV, fun g hg y hy => hAB (show (g, y) ∈ A ×ˢ B from ⟨hg, hy⟩)⟩
  choose A B C i hA hB hC hCV hABC using hlocal
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x : X => interior (B x))
    (fun _ => isOpen_interior)
    (fun x _ => mem_iUnion.mpr ⟨x, mem_interior_iff_mem_nhds.mpr (hB x)⟩)
  refine ⟨⋂ z ∈ s, A z, (biInter_finset_mem s).mpr (fun z _ => hA z), fun x => ?_⟩
  obtain ⟨z, hz, hzx⟩ := mem_iUnion₂.mp (hs (mem_univ x))
  refine ⟨i z, (closure_minimal ?_ (hC z)).trans (hCV z)⟩
  rintro _ ⟨g, hg, rfl⟩
  exact hABC z g ((mem_iInter₂.mp hg) z hz) x (interior_subset hzx)

/-- A compact Hausdorff flow with a dense orbit is metrisable if its
acting group is first-countable and the orbit point is fixed by a
co-precompact subgroup. -/
theorem metrizableSpace_of_dense_orbit_coprecompact_fixedPoint
    [FirstCountableTopology G] (H : Subgroup G) (hH : CoPrecompact G H)
    (x : X) (hx : Dense (orbit G x)) (hfix : ∀ h : H, (h : G) • x = x) :
    MetrizableSpace X := by
  classical
  obtain ⟨U, hU⟩ := (𝓝 (1 : G)).exists_antitone_basis
  choose F hF using fun n => hH (U n) (hU.1.mem_of_mem (show True from trivial))
  let K (n : ℕ) (f : F n) : Set X := closure ((fun g : G => g • ((f : G) • x)) '' U n)
  have hK (n : ℕ) (z : X) : ∃ f : F n, z ∈ K n f := by
    have horbit : orbit G x ⊆ ⋃ f : F n, K n f := by
      rintro _ ⟨g, rfl⟩
      obtain ⟨f, hf, u, hu, h, rfl⟩ := hF n g
      refine mem_iUnion.mpr ⟨⟨f, hf⟩, subset_closure ?_⟩
      exact ⟨u, hu, by simp only [mul_smul, hfix]⟩
    have hclosed : IsClosed (⋃ f : F n, K n f) :=
      isClosed_iUnion_of_finite fun _ => isClosed_closure
    have hsub := closure_minimal horbit hclosed
    rw [hx.closure_eq] at hsub
    exact mem_iUnion.mp (hsub (mem_univ z))
  let B (i : Σ n : ℕ, Finset (F n)) : Set X :=
    (⋃ f ∈ i.2, K i.1 f)ᶜ
  have hB : TopologicalSpace.IsTopologicalBasis (range B) := by
    refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
    · rintro _ ⟨i, rfl⟩
      exact (isClosed_biUnion_finset (fun _ _ => isClosed_closure)).isOpen_compl
    · intro z V hz hV
      let W (b : Bool) : Set X := if b then V else {z}ᶜ
      have hWo (b : Bool) : IsOpen (W b) := by
        cases b
        · exact isClosed_singleton.isOpen_compl
        · exact hV
      have hWcov (y : X) : ∃ b, y ∈ W b := by
        by_cases e : y = z
        · exact ⟨true, by simpa only [W, ite_true, e] using hz⟩
        · exact ⟨false, by simpa only [W, Bool.false_eq_true, ite_false, mem_compl_iff,
            mem_singleton_iff] using e⟩
      obtain ⟨A, hA, hAW⟩ := exists_closed_moves_refine_open_cover (G := G) W hWo hWcov
      obtain ⟨n, -, hn⟩ := (hU.1.mem_iff.mp hA)
      have small (f : F n) : z ∈ K n f → K n f ⊆ V := by
        intro hzK
        obtain ⟨b, hb⟩ := hAW ((f : G) • x)
        have hsub : K n f ⊆ W b := (closure_mono (image_mono hn)).trans hb
        cases b
        · exact False.elim ((hsub hzK) (mem_singleton z))
        · exact hsub
      let bad : Finset (F n) := Finset.univ.filter (fun f => ¬ K n f ⊆ V)
      refine ⟨B ⟨n, bad⟩, mem_range_self _, ?_, ?_⟩
      · intro hz'
        obtain ⟨f, hf, hfz⟩ := mem_iUnion₂.mp hz'
        exact (Finset.mem_filter.mp hf).2 (small f hfz)
      · intro y hy
        obtain ⟨f, hfy⟩ := hK n y
        by_contra hnV
        exact hy (mem_iUnion₂.mpr ⟨f, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          fun h => hnV (h hfy)⟩, hfy⟩)
  let _ : SecondCountableTopology X := hB.secondCountableTopology (countable_range B)
  infer_instance

/-- Every minimal compact Hausdorff flow of a first-countable group is
metrisable if the group has a co-precompact extremely amenable subgroup.
In particular, this applies to its universal minimal flow. -/
theorem metrizableSpace_of_coprecompact_extremelyAmenable
    [FirstCountableTopology G] [Nonempty X] [IsMinimal G X]
    (H : Subgroup G) (hH : CoPrecompact G H) (hfixed : CompactFlowFixedPoint.{0, v} H) :
    MetrizableSpace X := by
  let : MulAction H X := MulAction.compHom X H.subtype
  let : ContinuousSMul H X := MulAction.continuousSMul_compHom continuous_subtype_val
  obtain ⟨x, hx⟩ := hfixed X
  exact metrizableSpace_of_dense_orbit_coprecompact_fixedPoint H hH x
    (MulAction.dense_orbit G x) hx

end SuccessorTree.NonPrecompact
