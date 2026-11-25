import BANANA.NonPrecompact.FiniteColouringCompactness
import Mathlib.Topology.Algebra.Group.ContinuousInv
import Mathlib.Topology.Algebra.MulAction

/-!
# Fixed points of colouring flows and finite palettes

For a discrete copy set, pulling a colouring back by the inverse action
defines a continuous action on the space of colourings. A fixed point in
an orbit closure is constant on orbits. If there are finitely many orbit
representatives, compactness gives a uniform finite support on which a
translate of a prescribed finite set uses at most that many colours.
-/

namespace SuccessorTree.NonPrecompact

open Set
open scoped Pointwise

universe uX uColour

variable {G : Type*} {X : Type uX} {Colour : Type uColour} [Group G] [MulAction G X]

/-- The action on colourings obtained by pulling back by the inverse. -/
@[instance_reducible] private def colouringAction : MulAction G (X → Colour) where
  smul g c x := c (g⁻¹ • x)
  one_smul c := by
    funext x
    change c ((1 : G)⁻¹ • x) = c x
    simp
  mul_smul g h c := by
    funext x
    change c ((g * h)⁻¹ • x) = c (h⁻¹ • g⁻¹ • x)
    rw [mul_inv_rev, mul_smul]

/-- The orbit closure of a colouring under a continuous action on a discrete
set acquires a fixed point from the compact-flow fixed-point property. -/
theorem exists_fixed_colouring_in_orbit_closure
    [TopologicalSpace G] [ContinuousInv G]
    [TopologicalSpace X] [DiscreteTopology X] [ContinuousSMul G X]
    [TopologicalSpace Colour] [CompactSpace Colour] [T2Space Colour]
    (fixedPoint : ∀ (Y : Type (max uX uColour)) [TopologicalSpace Y] [CompactSpace Y]
      [T2Space Y] [Nonempty Y] [MulAction G Y] [ContinuousSMul G Y],
        ∃ y : Y, ∀ g : G, g • y = y)
    (c : X → Colour) :
    ∃ d ∈ closure (range fun g : G => fun x => c (g⁻¹ • x)),
      ∀ (g : G) (x : X), d (g • x) = d x := by
  letI : MulAction G (X → Colour) := colouringAction
  letI : ContinuousSMul G (X → Colour) := ⟨continuous_pi fun x => by
    rw [continuous_iff_continuousAt]
    intro p
    have hindex : ContinuousAt (fun q : G × (X → Colour) => q.1⁻¹ • x) p :=
      (continuous_fst.inv.smul continuous_const).continuousAt
    rw [ContinuousAt, nhds_discrete X, Filter.tendsto_pure] at hindex
    have hvalue : ContinuousAt (fun q : G × (X → Colour) => q.2 (p.1⁻¹ • x)) p :=
      ((continuous_apply (p.1⁻¹ • x)).comp continuous_snd).continuousAt
    apply hvalue.congr
    filter_upwards [hindex] with q hq
    change q.2 (p.1⁻¹ • x) = q.2 (q.1⁻¹ • x)
    rw [hq]⟩
  let Y : Set (X → Colour) := closure (MulAction.orbit G c)
  letI : CompactSpace Y := isCompact_iff_compactSpace.mp isClosed_closure.isCompact
  letI : Nonempty Y := ⟨⟨c, subset_closure (MulAction.mem_orbit_self c)⟩⟩
  let invariance (g : G) (d : Y) : g • d.val ∈ Y :=
    smul_closure_orbit_subset g c ⟨d.val, d.property, rfl⟩
  letI : MulAction G Y :=
    { smul := fun g d => ⟨g • d.val, invariance g d⟩
      one_smul := fun d => Subtype.ext (one_smul G d.val)
      mul_smul := fun g h d => Subtype.ext (mul_smul g h d.val) }
  letI : ContinuousSMul G Y := ⟨(continuous_fst.smul
    (continuous_subtype_val.comp continuous_snd)).subtype_mk _⟩
  obtain ⟨d, hd⟩ := fixedPoint Y
  refine ⟨d.val, d.property, fun g x => ?_⟩
  have heq := congrFun (congrArg Subtype.val (hd g⁻¹)) x
  change d.val ((g⁻¹)⁻¹ • x) = d.val x at heq
  simpa only [inv_inv] using heq

/-- The uniform finite collection of translates can be chosen before the
colouring. Consequently an ambient structure can contain all points of
each moved target, even when its small copies do not cover the target. -/
theorem exists_finite_translates_of_orbit_fixed_colourings
    [TopologicalSpace Colour] [CompactSpace Colour] [DiscreteTopology Colour]
    (T reps : Finset X)
    (hrep : ∀ x : X, ∃ r ∈ reps, ∃ g : G, g • r = x)
    (hfixed : ∀ c : X → Colour,
      ∃ d ∈ closure (range fun g : G => fun x => c (g⁻¹ • x)),
        ∀ (g : G) (x : X), d (g • x) = d x) :
    ∃ K : Finset G, ∀ c : X → Colour,
      ∃ g ∈ K, ∃ palette : Finset Colour, palette.card ≤ reps.card ∧
        ∀ x ∈ T, c (g • x) ∈ palette := by
  classical
  let support (g : G) : Finset X := T.image (fun x => g • x)
  let good (g : G) (c : support g → Colour) : Prop :=
    ∃ palette : Finset Colour, palette.card ≤ reps.card ∧ ∀ x, c x ∈ palette
  have hglobal (c : X → Colour) : ∃ g, good g ((support g).restrict c) := by
    obtain ⟨d, hd, hdFixed⟩ := hfixed c
    let U : Set (X → Colour) := (T.restrict) ⁻¹' {T.restrict d}
    have hU : IsOpen U := (isOpen_discrete _).preimage T.continuous_restrict
    obtain ⟨_, hmatch, g, rfl⟩ := mem_closure_iff.mp hd U hU rfl
    refine ⟨g⁻¹, reps.image d, Finset.card_image_le, ?_⟩
    intro x
    obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp x.property
    obtain ⟨r, hr, k, hk⟩ := hrep y
    have heq : c (g⁻¹ • y) = d y :=
      congrFun (show T.restrict (fun x => c (g⁻¹ • x)) = T.restrict d from hmatch) ⟨y, hy⟩
    refine Finset.mem_image.mpr ⟨r, hr, ?_⟩
    change d r = c x.val
    rw [← hyx, heq, ← hk, hdFixed]
  obtain ⟨K, hK⟩ := exists_finite_witnesses_of_colourings support good hglobal
  refine ⟨K, fun c => ?_⟩
  obtain ⟨g, hg, palette, hp, hpalette⟩ := hK c
  refine ⟨g, hg, palette, hp, fun x hx => ?_⟩
  exact hpalette ⟨g • x, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩

/-- Fixed points in colouring orbit closures give a uniform finite
set of coordinates containing a translate with a bounded palette. -/
theorem exists_finite_support_of_orbit_fixed_colourings
    [TopologicalSpace Colour] [CompactSpace Colour] [DiscreteTopology Colour]
    [Nonempty Colour]
    (T reps : Finset X)
    (hrep : ∀ x : X, ∃ r ∈ reps, ∃ g : G, g • r = x)
    (hfixed : ∀ c : X → Colour,
      ∃ d ∈ closure (range fun g : G => fun x => c (g⁻¹ • x)),
        ∀ (g : G) (x : X), d (g • x) = d x) :
    ∃ S : Finset X, ∀ c : S → Colour,
      ∃ (g : G) (h : ∀ x ∈ T, g • x ∈ S) (palette : Finset Colour),
        palette.card ≤ reps.card ∧
        ∀ (x : X) (hx : x ∈ T), c ⟨g • x, h x hx⟩ ∈ palette := by
  classical
  obtain ⟨K, hK⟩ := exists_finite_translates_of_orbit_fixed_colourings T reps hrep hfixed
  let S := K.biUnion fun g => T.image fun x => g • x
  refine ⟨S, fun c => ?_⟩
  let padded : X → Colour := fun x =>
    if hx : x ∈ S then c ⟨x, hx⟩ else Classical.choice ‹Nonempty Colour›
  obtain ⟨g, hg, palette, hp, hpalette⟩ := hK padded
  have hin (x : X) (hx : x ∈ T) : g • x ∈ S :=
    Finset.mem_biUnion.mpr ⟨g, hg, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩
  refine ⟨g, hin, palette, hp, fun x hx => ?_⟩
  simpa only [padded, dite_eq_left (hin x hx)] using hpalette x hx

end SuccessorTree.NonPrecompact
