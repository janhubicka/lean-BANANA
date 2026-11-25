import BANANA.NonPrecompact.UniversalMinimalFlow
import Mathlib.Topology.Compactification.StoneCech
import Mathlib.Algebra.Group.Action.TransferInstance

/-!
# Existence of universal minimal flows

Every compact Hausdorff minimal flow is homeomorphic to a quotient of the
Stone–Čech compactification of the discrete underlying set of the group.
Thus quotients of one small type suffice to index the product construction,
even when the target flow has a larger universe.
-/

namespace SuccessorTree.NonPrecompact

open Set Function Topology MulAction
open scoped Pointwise

universe u w

variable (G : Type u) [Group G] [TopologicalSpace G]

private abbrev DiscreteCompactification :=
  StoneCech (WithDiscreteTopology G)

omit [TopologicalSpace G] in
private theorem surjective_stoneCechOrbitMap
    {Y : Type w} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    [MulAction G Y] [IsMinimal G Y] (y : Y) :
    Surjective (stoneCechExtend (continuous_of_discreteTopology :
      Continuous (fun g : WithDiscreteTopology G => g.ofTopology • y))) := by
  let f := stoneCechExtend (continuous_of_discreteTopology :
    Continuous (fun g : WithDiscreteTopology G => g.ofTopology • y))
  have hclosed : IsClosed (range f) :=
    (isCompact_range (continuous_stoneCechExtend _)).isClosed
  have hd : Dense (range f) := (denseRange_smul G y).mono (by
    rintro _ ⟨g, rfl⟩
    exact ⟨stoneCechUnit (WithTopology.toTopology ⊥ g),
      stoneCechExtend_stoneCechUnit _ _⟩)
  exact range_eq_univ.mp (hclosed.closure_eq ▸ hd.closure_eq)

private structure FlowQuotient where
  rel : Setoid (DiscreteCompactification G)
  topology : TopologicalSpace (Quotient rel)
  compact : @CompactSpace _ topology
  hausdorff : @T2Space _ topology
  action : MulAction G (Quotient rel)
  continuousAction : @ContinuousSMul G _ action.toSMul _ topology

namespace FlowQuotient

private abbrev Carrier (F : FlowQuotient G) := Quotient F.rel

private instance (F : FlowQuotient G) : TopologicalSpace F.Carrier := F.topology
private instance (F : FlowQuotient G) : CompactSpace F.Carrier := F.compact
private instance (F : FlowQuotient G) : T2Space F.Carrier := F.hausdorff
private instance (F : FlowQuotient G) : MulAction G F.Carrier := F.action
private instance (F : FlowQuotient G) : ContinuousSMul G F.Carrier := F.continuousAction

private theorem exists_equivariant_homeomorph
    (Y : Type w) [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [Nonempty Y]
    [MulAction G Y] [ContinuousSMul G Y] [IsMinimal G Y] :
    ∃ (F : FlowQuotient G) (e : F.Carrier ≃ₜ Y),
      ∀ (g : G) (x : F.Carrier), e (g • x) = g • e x := by
  classical
  let y : Y := Classical.choice ‹Nonempty Y›
  let f : DiscreteCompactification G → Y :=
    stoneCechExtend (continuous_of_discreteTopology :
      Continuous (fun g : WithDiscreteTopology G => g.ofTopology • y))
  let r : Setoid (DiscreteCompactification G) :=
    ⟨fun a b => f a = f b, ⟨fun _ => rfl, Eq.symm, Eq.trans⟩⟩
  let p : Quotient r → Y := Quotient.lift f (fun _ _ h => h)
  have hp : Bijective p := ⟨by
    intro a b
    induction a using Quotient.inductionOn
    induction b using Quotient.inductionOn
    exact fun h => Quotient.sound (s := r) h, by
    intro z
    obtain ⟨a, ha⟩ := surjective_stoneCechOrbitMap G y z
    exact ⟨Quotient.mk r a, ha⟩⟩
  let e : Quotient r ≃ Y := Equiv.ofBijective p hp
  let _ : TopologicalSpace (Quotient r) := TopologicalSpace.induced e inferInstance
  let E : Quotient r ≃ₜ Y := e.toHomeomorphOfIsInducing ⟨rfl⟩
  let _ : CompactSpace (Quotient r) := E.symm.compactSpace
  let _ : T2Space (Quotient r) := T2Space.of_injective_continuous E.injective E.continuous
  let _ : MulAction G (Quotient r) := e.mulAction G
  have he (g : G) (a : Quotient r) : E (g • a) = g • E a :=
    e.apply_symm_apply _
  let _ : ContinuousSMul G (Quotient r) := ⟨E.isInducing.continuous_iff.mpr (by
    simp only [Function.comp_def, he]
    exact continuous_fst.smul (E.continuous.comp continuous_snd))⟩
  exact ⟨⟨r, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩, E, he⟩

end FlowQuotient

/-- Every topological group has a compact Hausdorff minimal flow universal
among other such flows, including those in a larger universe. -/
theorem exists_universalMinimalFlow :
    ∃ (M : Type u) (_ : TopologicalSpace M) (_ : CompactSpace M) (_ : T2Space M)
      (_ : Nonempty M) (_ : MulAction G M) (_ : ContinuousSMul G M)
      (_ : IsMinimal G M), UniversalAmongMinimalFlows.{u,u,w} G M := by
  let X := (F : FlowQuotient G) → F.Carrier
  let _ : Nonempty X := ⟨fun F => Quotient.mk F.rel
    (stoneCechUnit (WithTopology.toTopology ⊥ (1 : G)))⟩
  obtain ⟨M, hMcompact, hMne, hMcont, hMmin⟩ := exists_compact_minimal_subaction G X
  let _ := hMcompact
  let _ := hMne
  let _ := hMcont
  let _ := hMmin
  refine ⟨M, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, ?_⟩
  intro Y _ _ _ _ _ _ _
  obtain ⟨F, e, he⟩ := FlowQuotient.exists_equivariant_homeomorph G Y
  let f (x : M) := e (x.val F)
  have hf : Continuous f :=
    e.continuous.comp ((continuous_apply F).comp continuous_subtype_val)
  have hact (g : G) (x : M) : f (g • x) = g • f x := he g (x.val F)
  refine ⟨f, hf, ?_, hact⟩
  apply range_eq_univ.mp
  apply (eq_empty_or_univ_of_smul_invariant_closed G (isCompact_range hf).isClosed ?_).resolve_left
  · exact (range_nonempty f).ne_empty
  · rintro g _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨g • x, hact g x⟩

end SuccessorTree.NonPrecompact
