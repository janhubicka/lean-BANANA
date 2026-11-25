import BANANA.NonPrecompact.UniversalMinimalFlow
import BANANA.NonPrecompact.FixedPointColouring

/-!
# Bounded colour palettes from a metrisable universal minimal flow

For one transitive discrete group action, the orbit closure of the
Stone–Čech unit contains a minimal flow. If this minimal flow is a factor
of a sequentially compact flow, transitivity and extremal disconnectedness
force a uniform finite range for its coordinate evaluations.
-/

namespace SuccessorTree.NonPrecompact

open Set Filter Function Topology MulAction
open scoped Pointwise

universe u v w

variable {G : Type u} {M : Type v} {X : Type w}
  [Group G] [TopologicalSpace G] [ContinuousInv G]
  [TopologicalSpace X] [DiscreteTopology X] [MulAction G X] [ContinuousSMul G X]

/-- A sequentially compact universal minimal flow forces a uniform finite
palette bound on translates of finite subsets of a transitive discrete action. -/
theorem exists_bounded_colour_palettes_of_seqCompact_universalMinimalFlow
    [TopologicalSpace M] [SeqCompactSpace M] [MulAction G M]
    (hU : UniversalAmongMinimalFlows.{u,v,w} G M)
    (x₀ : X) (hX : ∀ x : X, ∃ g : G, g • x₀ = x) :
    ∃ d : ℕ, ∀ {Colour : Type*} [TopologicalSpace Colour] [CompactSpace Colour]
      [T2Space Colour] [DiscreteTopology Colour] (T : Finset X) (c : X → Colour),
      ∃ (g : G) (palette : Finset Colour), palette.card ≤ d ∧
        ∀ x ∈ T, c (g • x) ∈ palette := by
  classical
  letI : ExtremallyDisconnected (StoneCech X) :=
    CompactT2.Projective.extremallyDisconnected StoneCech.projective
  letI : MulAction G (X → StoneCech X) := colouringAction
  letI : ContinuousSMul G (X → StoneCech X) := continuous_colouringAction
  let Ω := closure (orbit G (stoneCechUnit : X → StoneCech X))
  letI : CompactSpace Ω := isCompact_iff_compactSpace.mp isClosed_closure.isCompact
  letI : Nonempty Ω := ⟨⟨stoneCechUnit, subset_closure (mem_orbit_self _)⟩⟩
  letI : MulAction G Ω := {
    smul := fun g x => ⟨g • x.val, smul_closure_orbit_subset g _ ⟨x.val, x.property, rfl⟩⟩
    one_smul := fun x => Subtype.ext (one_smul G x.val)
    mul_smul := fun g h x => Subtype.ext (mul_smul g h x.val) }
  letI : ContinuousSMul G Ω := ⟨(continuous_fst.smul
    (continuous_subtype_val.comp continuous_snd)).subtype_mk _⟩
  obtain ⟨Y, hYcompact, hYne, hYcont, hYmin⟩ := exists_compact_minimal_subaction G Ω
  let _ := hYcompact
  let _ := hYne
  let _ := hYcont
  let _ := hYmin
  obtain ⟨φ, hφ, hs, _⟩ := hU Y
  let F := range fun y : Y => y.val.val x₀
  have hFinite : F.Finite := by
    have hq := finite_range_of_seqCompact_extremallyDisconnected
      ((continuous_apply x₀).comp
        (continuous_subtype_val.comp (continuous_subtype_val.comp hφ)))
    convert hq using 1
    ext z
    exact ⟨fun ⟨y, hy⟩ => by
      obtain ⟨m, rfl⟩ := hs y
      exact ⟨m, hy⟩, fun ⟨m, hm⟩ => ⟨φ m, hm⟩⟩
  refine ⟨hFinite.toFinset.card, ?_⟩
  intro Colour _ _ _ _ T c
  let y : Y := Classical.choice ‹Nonempty Y›
  have hF (x : X) : y.val.val x ∈ F := by
    obtain ⟨g, rfl⟩ := hX x
    refine ⟨g⁻¹ • y, ?_⟩
    change y.val.val ((g⁻¹)⁻¹ • x₀) = y.val.val (g • x₀)
    rw [inv_inv]
  let cβ := stoneCechExtend (continuous_of_discreteTopology : Continuous c)
  let restrict (z : X → StoneCech X) : T → Colour := fun x => cβ (z x)
  have hrestrict : Continuous restrict :=
    continuous_pi fun x => (continuous_stoneCechExtend _).comp (continuous_apply (x : X))
  let N := restrict ⁻¹' {restrict y.val.val}
  have ho : IsOpen N := (isOpen_discrete _).preimage hrestrict
  have hy : y.val.val ∈ closure (orbit G (stoneCechUnit : X → StoneCech X)) := y.val.property
  obtain ⟨_, hN, g, rfl⟩ := mem_closure_iff.mp hy N ho rfl
  refine ⟨g⁻¹, hFinite.toFinset.image cβ, Finset.card_image_le, fun x hx => ?_⟩
  have he := congrFun (show restrict (g • stoneCechUnit) = restrict y.val.val from hN)
    (⟨x, hx⟩ : T)
  change cβ (stoneCechUnit (g⁻¹ • x)) = cβ (y.val.val x) at he
  rw [show cβ (stoneCechUnit (g⁻¹ • x)) = c (g⁻¹ • x) from
    stoneCechExtend_stoneCechUnit _ _] at he
  rw [he]
  exact Finset.mem_image.mpr ⟨y.val.val x, hFinite.mem_toFinset.mpr (hF x), rfl⟩

end SuccessorTree.NonPrecompact
