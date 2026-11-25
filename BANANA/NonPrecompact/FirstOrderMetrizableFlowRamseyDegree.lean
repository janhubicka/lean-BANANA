import BANANA.NonPrecompact.CoprecompactFixedPointMetrizability
import BANANA.NonPrecompact.StoneCechOrbitFlow
import BANANA.NonPrecompact.UniversalMinimalFlowExistence

/-!
# Ramsey degrees from a metrisable universal minimal flow

Apply the Stone–Čech palette bound to the discrete action on embeddings.
Compactness chooses a finite list of possible translates before a
colouring is given, and local finiteness provides a finite ambient
structure containing all the translated targets.
-/

namespace SuccessorTree.NonPrecompact

open Filter FirstOrder Set Topology TopologicalSpace
open scoped FirstOrder

universe uA uM v

variable {L : Language} {M : Type uM} [L.Structure M]
variable {A : Type uA} [L.Structure A] [Finite A]
variable {Flow : Type v} [TopologicalSpace Flow] [MulAction (FirstOrderAut L M) Flow]

/-- A sequentially compact universal minimal flow gives finite embedding
Ramsey degrees for the age of a locally finite ultrahomogeneous structure. -/
theorem firstOrderFiniteEmbeddingDegree_of_seqCompact_universalMinimalFlow
    [SeqCompactSpace Flow]
    (hU : UniversalAmongMinimalFlows.{uM, v, max uA uM} (FirstOrderAut L M) Flow)
    (hM : L.IsUltrahomogeneous M) (e : A ↪[L] M)
    (hLoc : ∀ s : Finset M, Finite (Language.Substructure.closure L (s : Set M))) :
    ∃ d : ℕ, ∀ (B : Type uM) [L.Structure B] [Finite B]
      (_ : B ↪[L] M) (r : ℕ), 0 < r →
      ∃ C : L.Substructure M, Finite C ∧
        ∀ c : (A ↪[L] C) → Fin r,
          ∃ f : B ↪[L] C, ∃ palette : Finset (Fin r), palette.card ≤ d ∧
            ∀ p : A ↪[L] B, c (f.comp p) ∈ palette := by
  classical
  let : TopologicalSpace (A ↪[L] M) := ⊥
  let : DiscreteTopology (A ↪[L] M) := ⟨rfl⟩
  let : ContinuousSMul (FirstOrderAut L M) (A ↪[L] M) :=
    FirstOrderAut.continuous_embedding_smul
  obtain ⟨d, hd⟩ := exists_bounded_colour_palettes_of_seqCompact_universalMinimalFlow
    hU e (FirstOrderAut.exists_smul_eq_embedding hM e)
  refine ⟨d, fun B _ _ b r hr => ?_⟩
  let : TopologicalSpace (Fin r) := ⊥
  let : DiscreteTopology (Fin r) := ⟨rfl⟩
  let : Finite (A ↪[L] B) := Finite.of_injective (fun p : A ↪[L] B => (p : A → B))
    DFunLike.coe_injective
  let : Fintype (A ↪[L] B) := Fintype.ofFinite _
  let T : Finset (A ↪[L] M) := Finset.univ.image fun p : A ↪[L] B => b.comp p
  obtain ⟨K, hK⟩ := exists_finite_translates_of_bounded_colour_palettes
    T d (fun c : (A ↪[L] M) → Fin r => hd T c)
  exact firstOrderEmbeddingPalette_in_finite_ambient b hLoc hr id K fun c => by
    obtain ⟨g, hg, palette, hp, hpalette⟩ := hK c
    exact ⟨g, hg, palette, hp, fun p =>
      hpalette (b.comp p) (Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩)⟩

/-- The implication from metrisability of the universal minimal flow to
finite embedding Ramsey degrees for a locally finite Fraïssé age. -/
theorem firstOrderFiniteEmbeddingDegree_of_metrizable_universalMinimalFlow
    [CompactSpace Flow] [MetrizableSpace Flow]
    (hU : UniversalAmongMinimalFlows.{uM, v, max uA uM} (FirstOrderAut L M) Flow)
    (hM : L.IsUltrahomogeneous M) (e : A ↪[L] M)
    (hLoc : ∀ s : Finset M, Finite (Language.Substructure.closure L (s : Set M))) :
    ∃ d : ℕ, ∀ (B : Type uM) [L.Structure B] [Finite B]
      (_ : B ↪[L] M) (r : ℕ), 0 < r →
      ∃ C : L.Substructure M, Finite C ∧
        ∀ c : (A ↪[L] C) → Fin r,
          ∃ f : B ↪[L] C, ∃ palette : Finset (Fin r), palette.card ≤ d ∧
            ∀ p : A ↪[L] B, c (f.comp p) ∈ palette :=
  firstOrderFiniteEmbeddingDegree_of_seqCompact_universalMinimalFlow hU hM e hLoc

/-- Metrisability of the universal minimal flow also bounds copy Ramsey
degrees in the finite age. -/
theorem firstOrderFiniteCopyDegree_of_metrizable_universalMinimalFlow
    [CompactSpace Flow] [MetrizableSpace Flow]
    (hU : UniversalAmongMinimalFlows.{uM, v, max uA uM} (FirstOrderAut L M) Flow)
    (hM : L.IsUltrahomogeneous M) (e : A ↪[L] M)
    (hLoc : ∀ s : Finset M, Finite (Language.Substructure.closure L (s : Set M))) :
    ∃ d : ℕ, ∀ (B : Type uM) [L.Structure B] [Finite B]
      (_ : B ↪[L] M) (r : ℕ), 0 < r →
      ∃ C : L.Substructure M, Finite C ∧
        ∀ c : FirstOrderCopy L A C → Fin r,
          ∃ f : B ↪[L] C, ∃ palette : Finset (Fin r), palette.card ≤ d ∧
            ∀ p : FirstOrderCopy L A B, c (FirstOrderCopy.map f p) ∈ palette :=
  firstOrderFiniteCopyDegree_of_embeddingDegree
    (firstOrderFiniteEmbeddingDegree_of_metrizable_universalMinimalFlow hU hM e hLoc)

/-- A countable first-order structure has a first-countable pointwise
automorphism group. Finite tuples index the neighbourhood bases. -/
theorem FirstOrderAut.firstCountableTopology_of_countable [Countable M] :
    FirstCountableTopology (FirstOrderAut L M) := by
  constructor
  intro g
  let eval (i : Σ n : ℕ, Fin n → M) : Set (FirstOrderAut L M) :=
    {h | ∀ j, h.toEquiv (i.2 j) = g.toEquiv (i.2 j)}
  have hBasis : (𝓝 g).HasBasis (fun _ => True) eval := by
    refine ⟨fun U => ?_⟩
    constructor
    · intro hU
      obtain ⟨n, a, h⟩ := FirstOrderAut.exists_tupleEval_subset_of_mem_nhds g U hU
      exact ⟨⟨n, a⟩, trivial, h⟩
    · rintro ⟨i, -, hi⟩
      exact Filter.mem_of_superset
        ((FirstOrderAut.isOpen_tupleEval i.2 (g • i.2)).mem_nhds (fun _ => rfl)) hi
  exact hBasis.isCountablyGenerated

/-- Finite copy Ramsey degrees via the manuscript's dynamical argument:
take the subgroup closure, establish metrisability of a universal minimal
flow and then pass from embedding Ramsey degrees to copy Ramsey degrees. -/
theorem firstOrderFiniteCopyDegree_of_coprecompactExtremelyAmenable_via_universalMinimalFlow
    {A₀ : Type uM} [L.Structure A₀] [Finite A₀] [Countable M]
    (hM : L.IsUltrahomogeneous M) (e : A₀ ↪[L] M)
    (hLoc : ∀ s : Finset M, Finite (Language.Substructure.closure L (s : Set M)))
    (H : Subgroup (FirstOrderAut L M))
    (hH : CoPrecompact (FirstOrderAut L M) H)
    (hfixed : CompactFlowFixedPoint.{uM, uM} H) :
    ∃ d : ℕ, ∀ (B : Type uM) [L.Structure B] [Finite B]
      (_ : B ↪[L] M) (r : ℕ), 0 < r →
      ∃ C : L.Substructure M, Finite C ∧
        ∀ c : FirstOrderCopy L A₀ C → Fin r,
          ∃ f : B ↪[L] C, ∃ palette : Finset (Fin r), palette.card ≤ d ∧
            ∀ p : FirstOrderCopy L A₀ B, c (FirstOrderCopy.map f p) ∈ palette := by
  let _ := FirstOrderAut.firstCountableTopology_of_countable (L := L) (M := M)
  obtain ⟨Y, _, _, _, _, _, _, _, hU⟩ :=
    exists_universalMinimalFlow.{uM, uM} (FirstOrderAut L M)
  let _ : MetrizableSpace Y := metrizableSpace_of_coprecompact_extremelyAmenable
    H.topologicalClosure (hH.mono H.le_topologicalClosure)
    (CompactFlowFixedPoint.topologicalClosure H hfixed)
  exact firstOrderFiniteCopyDegree_of_metrizable_universalMinimalFlow hU hM e hLoc

end SuccessorTree.NonPrecompact
