import BANANA.NonPrecompact.BananaLimitExtremelyAmenableDegree
import BANANA.NonPrecompact.StoneCechOrbitFlow
import BANANA.NonPrecompact.UniversalMinimalFlowExistence

/-!
# The universal minimal flow of the native BANANA group is not metrisable

This proof uses a single automorphism action on finite embeddings.
Any metrisable universal minimal flow would impose a finite copy degree
on a line pair by its factor map onto a minimal Stone–Čech orbit flow.
-/

namespace SuccessorTree.NonPrecompact
open TopologicalSpace

/-- For the actual native pointwise group, every universal minimal flow
is nonmetrisable. Universality among small flows suffices. -/
theorem bananaLimit_universalMinimalFlow_not_metrizable
    {M : Type v} [TopologicalSpace M] [CompactSpace M]
    [MulAction BananaLimitAutomorphism M]
    (hU : UniversalAmongMinimalFlows.{0,v,0} BananaLimitAutomorphism M) :
    ¬ MetrizableSpace M := by
  intro hmetr
  letI : MetrizableSpace M := hmetr
  let A := linePairSource (0 : F2)
  let X := BananaMatrixEmbeddingToLimit A
  letI : TopologicalSpace X := ⊥
  letI : DiscreteTopology X := ⟨rfl⟩
  letI : ContinuousSMul BananaLimitAutomorphism X :=
    BananaMatrixEmbeddingToLimit.continuous_automorphism_smul
  obtain ⟨e⟩ := A.embeds_in_explicit_limit
  obtain ⟨d, hd⟩ := exists_bounded_colour_palettes_of_seqCompact_universalMinimalFlow
    hU e e.exists_automorphism_smul_eq
  apply A.copyRamseyDegree_infinite_of_positive (by decide) (by decide) d
  apply A.copyRamseyDegreeLE_of_finite_translates d
  intro r _ T
  letI : TopologicalSpace (Fin r) := ⊥
  letI : DiscreteTopology (Fin r) := ⟨rfl⟩
  exact exists_finite_translates_of_bounded_colour_palettes T d fun c => hd T c

/-- The native BANANA group has a nonmetrisable universal minimal flow. -/
theorem bananaLimit_exists_nonmetrizable_universalMinimalFlow :
    ∃ (M : Type) (_ : TopologicalSpace M) (_ : CompactSpace M) (_ : T2Space M)
      (_ : Nonempty M) (_ : MulAction BananaLimitAutomorphism M)
      (_ : ContinuousSMul BananaLimitAutomorphism M)
      (_ : MulAction.IsMinimal BananaLimitAutomorphism M),
      UniversalAmongMinimalFlows.{0,0,0} BananaLimitAutomorphism M ∧
        ¬ MetrizableSpace M := by
  obtain ⟨M, ht, hc, hT2, hne, hact, hcont, hmin, hU⟩ :=
    exists_universalMinimalFlow.{0,0} BananaLimitAutomorphism
  exact ⟨M, ht, hc, hT2, hne, hact, hcont, hmin, hU,
    bananaLimit_universalMinimalFlow_not_metrizable hU⟩

end SuccessorTree.NonPrecompact
