import BANANA.NonPrecompact.BananaLimitTopologicalAmenability
import Mathlib.Topology.MetricSpace.Polish

/-!
# The native BANANA automorphism group is Polish

Record each automorphism and its inverse by their point evaluations. The
equations expressing inverse maps, linearity and preservation of the
pairing define a closed subspace of a countable product of discrete spaces.
-/

namespace SuccessorTree.NonPrecompact

open Function Set TopologicalSpace Topology

local instance : TopologicalSpace BananaLimitVector := ⊥
local instance : DiscreteTopology BananaLimitVector := ⟨rfl⟩
local instance : TopologicalSpace F2 := ⊥
local instance : DiscreteTopology F2 := ⟨rfl⟩

private abbrev Evaluation := (BananaLimitVector ⊕ BananaLimitVector) → BananaLimitVector
private abbrev EvaluationPair := Evaluation × Evaluation

/-- Forward and inverse point evaluations on the original two sorts. -/
noncomputable def bananaLimitAutomorphismEvaluations (g : BananaLimitAutomorphism) : EvaluationPair :=
  (bananaLimitEvaluation g, bananaLimitEvaluation g⁻¹)

private def IsLinearPermutationOn (tag : BananaLimitVector → BananaLimitVector ⊕ BananaLimitVector)
    (p : EvaluationPair) : Prop :=
  LeftInverse (p.2 ∘ tag) (p.1 ∘ tag) ∧
  RightInverse (p.2 ∘ tag) (p.1 ∘ tag) ∧
  (∀ x y, p.1 (tag (x + y)) = p.1 (tag x) + p.1 (tag y)) ∧
  ∀ (r : F2) x, p.1 (tag (r • x)) = r • p.1 (tag x)

private def IsAutomorphismEvaluation (p : EvaluationPair) : Prop :=
  IsLinearPermutationOn Sum.inl p ∧ IsLinearPermutationOn Sum.inr p ∧
  ∀ x y, bananaLimitPairing (p.1 (.inl x)) (p.1 (.inr y)) = bananaLimitPairing x y

private theorem continuous_pointEvaluation (tag : BananaLimitVector → BananaLimitVector ⊕ BananaLimitVector) :
    Continuous (fun q : Evaluation × BananaLimitVector => q.1 (tag q.2)) :=
  continuous_prod_of_discrete_right.mpr fun y => continuous_apply (tag y)

private theorem isClosed_linearPermutationOn (tag : BananaLimitVector → BananaLimitVector ⊕ BananaLimitVector) :
    IsClosed {p : EvaluationPair | IsLinearPermutationOn tag p} := by
  have hf (x : BananaLimitVector) : Continuous (fun p : EvaluationPair => p.1 (tag x)) :=
    (continuous_apply (tag x)).comp continuous_fst
  have hg (x : BananaLimitVector) : Continuous (fun p : EvaluationPair => p.2 (tag x)) :=
    (continuous_apply (tag x)).comp continuous_snd
  have hinvL : IsClosed (⋂ x, {p : EvaluationPair | p.2 (tag (p.1 (tag x))) = x}) :=
    isClosed_iInter fun x => isClosed_eq
      ((continuous_pointEvaluation tag).comp (continuous_snd.prodMk (hf x))) continuous_const
  have hinvR : IsClosed (⋂ x, {p : EvaluationPair | p.1 (tag (p.2 (tag x))) = x}) :=
    isClosed_iInter fun x => isClosed_eq
      ((continuous_pointEvaluation tag).comp (continuous_fst.prodMk (hg x))) continuous_const
  have haddFn : Continuous (fun q : BananaLimitVector × BananaLimitVector => q.1 + q.2) :=
    continuous_of_discreteTopology
  have hadd : IsClosed (⋂ x, ⋂ y, {p : EvaluationPair |
      p.1 (tag (x + y)) = p.1 (tag x) + p.1 (tag y)}) :=
    isClosed_iInter fun x => isClosed_iInter fun y => isClosed_eq (hf (x + y))
      (haddFn.comp ((hf x).prodMk (hf y)))
  have hsmul : IsClosed (⋂ (r : F2), ⋂ x, {p : EvaluationPair |
      p.1 (tag (r • x)) = r • p.1 (tag x)}) :=
    isClosed_iInter fun r => isClosed_iInter fun x => isClosed_eq (hf (r • x))
      (continuous_of_discreteTopology.comp (hf x))
  convert hinvL.inter (hinvR.inter (hadd.inter hsmul)) using 1
  ext p
  simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter, IsLinearPermutationOn,
    LeftInverse, RightInverse, comp_apply]

private theorem isClosed_automorphismEvaluation :
    IsClosed {p : EvaluationPair | IsAutomorphismEvaluation p} := by
  have hpairFn : Continuous (fun q : BananaLimitVector × BananaLimitVector =>
      bananaLimitPairing q.1 q.2) := continuous_of_discreteTopology
  have hpair : IsClosed (⋂ x, ⋂ y, {p : EvaluationPair |
      bananaLimitPairing (p.1 (.inl x)) (p.1 (.inr y)) = bananaLimitPairing x y}) := by
    apply isClosed_iInter
    intro x
    apply isClosed_iInter
    intro y
    have hcoordinates : Continuous (fun p : EvaluationPair => (p.1 (.inl x), p.1 (.inr y))) :=
      ((continuous_apply (Sum.inl x)).comp continuous_fst).prodMk
        ((continuous_apply (Sum.inr y)).comp continuous_fst)
    exact isClosed_eq (hpairFn.comp hcoordinates) continuous_const
  convert (isClosed_linearPermutationOn Sum.inl).inter
    ((isClosed_linearPermutationOn Sum.inr).inter hpair) using 1
  ext p
  simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter, IsAutomorphismEvaluation]

private def decodeSort {tag : BananaLimitVector → BananaLimitVector ⊕ BananaLimitVector}
    {p : EvaluationPair} (h : IsLinearPermutationOn tag p) :
    BananaLimitVector ≃ₗ[F2] BananaLimitVector where
  toFun := p.1 ∘ tag
  invFun := p.2 ∘ tag
  left_inv := h.1
  right_inv := h.2.1
  map_add' := h.2.2.1
  map_smul' := h.2.2.2

private theorem evaluations_range :
    range bananaLimitAutomorphismEvaluations = {p : EvaluationPair | IsAutomorphismEvaluation p} := by
  ext p
  constructor
  · rintro ⟨g, rfl⟩
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, g.property⟩
    · exact g.val.1.symm_apply_apply
    · exact g.val.1.apply_symm_apply
    · exact g.val.1.map_add
    · exact g.val.1.map_smul
    · exact g.val.2.symm_apply_apply
    · exact g.val.2.apply_symm_apply
    · exact g.val.2.map_add
    · exact g.val.2.map_smul
  · intro hp
    refine ⟨⟨(decodeSort hp.1, decodeSort hp.2.1), hp.2.2⟩, ?_⟩
    apply Prod.ext <;> funext x <;> cases x <;> rfl

/-- The evaluation graph realises the native group as a closed subspace. -/
theorem isClosedEmbedding_bananaLimitAutomorphismEvaluations :
    IsClosedEmbedding bananaLimitAutomorphismEvaluations := by
  have hforward : IsInducing bananaLimitEvaluation := ⟨rfl⟩
  have hinv : Continuous (fun g : BananaLimitAutomorphism => bananaLimitEvaluation g⁻¹) :=
    hforward.continuous.comp continuous_inv
  refine ⟨⟨.of_comp (hforward.continuous.prodMk hinv) continuous_fst hforward, ?_⟩, ?_⟩
  · intro g h he
    have hf := congrArg Prod.fst he
    apply Subtype.ext
    apply Prod.ext <;> apply LinearEquiv.ext
    · exact fun x => congrFun hf (.inl x)
    · exact fun x => congrFun hf (.inr x)
  · rw [evaluations_range]
    exact isClosed_automorphismEvaluation

/-- The pointwise automorphism group of the countable native BANANA pairing is Polish. -/
theorem bananaLimitAutomorphism_polishSpace : PolishSpace BananaLimitAutomorphism := by
  let : PolishSpace EvaluationPair := by constructor
  exact isClosedEmbedding_bananaLimitAutomorphismEvaluations.polishSpace

end SuccessorTree.NonPrecompact
