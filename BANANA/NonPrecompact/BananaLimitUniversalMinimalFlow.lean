import BANANA.NonPrecompact.BananaLimitExtremelyAmenableDegree
import BANANA.NonPrecompact.StoneCechOrbitFlow

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

end SuccessorTree.NonPrecompact
