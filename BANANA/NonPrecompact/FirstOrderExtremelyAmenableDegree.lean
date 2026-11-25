import BANANA.NonPrecompact.FirstOrderPointwiseAutomorphism
import BANANA.NonPrecompact.FixedPointColouring
import BANANA.NonPrecompact.OrbitCover
import Mathlib.Topology.Algebra.Group.Subgroup

/-!
# A direct finite Ramsey-degree bound from extreme amenability

For a locally finite ultrahomogeneous first-order structure, the finite
`UFH` covering property and extreme amenability of a subgroup of its
pointwise automorphism group imply finite embedding and copy Ramsey
degrees. The proof uses the colouring-flow fixed point, the finite
witnesses from compactness, and a finite ambient substructure containing
all those moved targets.
-/

namespace SuccessorTree.NonPrecompact

open FirstOrder Set Filter Topology MulAction
open scoped FirstOrder

universe uA uM uB

variable {L : Language} {M : Type uM} [L.Structure M]
variable {A : Type uA} [L.Structure A] [Finite A]

/-- On finite first-order embeddings, co-precompactness has an actual
finite set of subgroup orbit representatives. -/
theorem FirstOrderAut.exists_finset_embeddingOrbitRepresentatives
    (hM : L.IsUltrahomogeneous M) (e : A ↪[L] M)
    (H : Subgroup (FirstOrderAut L M)) (hH : CoPrecompact (FirstOrderAut L M) H) :
    ∃ R : Finset (A ↪[L] M), ∀ x : A ↪[L] M, ∃ r ∈ R, ∃ h : H, h • r = x := by
  exact exists_finset_orbitRepresentatives_of_coprecompact H hH e
    (FirstOrderAut.isOpen_embedding_eval e e)
    (FirstOrderAut.exists_smul_eq_embedding hM e)

/-- The maximal fixed-point property used for the colour-flow universe.
This is the definition of extreme amenability at that universe. -/
def CompactFlowFixedPoint (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  ∀ (Y : Type (max uA uM)) [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    [Nonempty Y] [MulAction G Y] [ContinuousSMul G Y], ∃ y : Y, ∀ g : G, g • y = y

variable {B : Type uB} [L.Structure B]

omit [Finite A] in
/-- If finitely many candidate translates suffice for every colouring of the
limit embeddings, a single finite ambient substructure works for all
colourings. It contains each entire candidate target. -/
theorem firstOrderEmbeddingPalette_in_finite_ambient [Finite B]
    (b : B ↪[L] M) (hLoc : ∀ s : Finset M, Finite (Language.Substructure.closure L (s : Set M)))
    {d r : ℕ} (hr : 0 < r) {Γ : Type*} (groupElement : Γ → FirstOrderAut L M) (K : Finset Γ)
    (hK : ∀ c : (A ↪[L] M) → Fin r, ∃ g ∈ K, ∃ palette : Finset (Fin r),
      palette.card ≤ d ∧ ∀ p : A ↪[L] B, c (groupElement g • b.comp p) ∈ palette) :
    ∃ C : L.Substructure M, Finite C ∧
      ∀ c : (A ↪[L] C) → Fin r,
        ∃ f : B ↪[L] C, ∃ palette : Finset (Fin r), palette.card ≤ d ∧
          ∀ p : A ↪[L] B, c (f.comp p) ∈ palette := by
  classical
  let : Fintype B := Fintype.ofFinite _
  let S : Finset M := K.biUnion fun g => Finset.univ.image fun x : B => groupElement g • b x
  let C := Language.Substructure.closure L (S : Set M)
  refine ⟨C, hLoc S, fun c => ?_⟩
  let padded (p : A ↪[L] M) : Fin r :=
    if hs : ∀ a, p a ∈ C then c (p.codRestrict C hs) else ⟨0, hr⟩
  obtain ⟨g, hg, palette, hp, hpalette⟩ := hK padded
  let fM : B ↪[L] M := (groupElement g).toEquiv.toEmbedding.comp b
  have hf (x : B) : fM x ∈ C := Language.Substructure.subset_closure
    (Finset.mem_biUnion.mpr ⟨g, hg, Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩⟩)
  let f : B ↪[L] C := fM.codRestrict C hf
  refine ⟨f, palette, hp, fun p => ?_⟩
  have hgood := hpalette p
  have hin : ∀ a, (groupElement g • b.comp p) a ∈ C := fun a => hf (p a)
  change (if hs : ∀ a, (groupElement g • b.comp p) a ∈ C then
    c ((groupElement g • b.comp p).codRestrict C hs) else ⟨0, hr⟩) ∈ palette at hgood
  rw [dite_eq_left hin] at hgood
  exact hgood

/-- In the finite age of a locally finite ultrahomogeneous first-order
structure, the orbit bound gives an embedding Ramsey-degree bound. The
finite ambient structure contains the entire moved target in every
selected translate, even if there were no small embeddings in that target. -/
theorem firstOrderFiniteEmbeddingDegree_of_coprecompactExtremelyAmenable
    (hM : L.IsUltrahomogeneous M) (e : A ↪[L] M)
    (hLoc : ∀ s : Finset M, Finite (Language.Substructure.closure L (s : Set M)))
    (H : Subgroup (FirstOrderAut L M))
    (hH : CoPrecompact (FirstOrderAut L M) H)
    (hfixed : CompactFlowFixedPoint.{uA, uM} H) :
    ∃ d : ℕ, ∀ (B : Type uM) [L.Structure B] [Finite B]
      (_ : B ↪[L] M) (r : ℕ), 0 < r →
      ∃ C : L.Substructure M, Finite C ∧
        ∀ c : (A ↪[L] C) → Fin r,
          ∃ f : B ↪[L] C, ∃ palette : Finset (Fin r), palette.card ≤ d ∧
            ∀ p : A ↪[L] B, c (f.comp p) ∈ palette := by
  classical
  obtain ⟨R, hR⟩ := FirstOrderAut.exists_finset_embeddingOrbitRepresentatives hM e H hH
  refine ⟨R.card, fun B _ _ b r hr => ?_⟩
  let : TopologicalSpace (A ↪[L] M) := ⊥
  let : DiscreteTopology (A ↪[L] M) := ⟨rfl⟩
  let : ContinuousSMul (FirstOrderAut L M) (A ↪[L] M) :=
    FirstOrderAut.continuous_embedding_smul
  let : TopologicalSpace (Fin r) := ⊥
  let : DiscreteTopology (Fin r) := ⟨rfl⟩
  let : Finite (A ↪[L] B) := Finite.of_injective (fun p : A ↪[L] B => (p : A → B))
    DFunLike.coe_injective
  let : Fintype (A ↪[L] B) := Fintype.ofFinite _
  let T : Finset (A ↪[L] M) := Finset.univ.image fun p : A ↪[L] B => b.comp p
  obtain ⟨K, hK⟩ := exists_finite_translates_of_orbit_fixed_colourings (G := H)
    (Colour := Fin r) T R hR (fun c => exists_fixed_colouring_in_orbit_closure hfixed c)
  exact firstOrderEmbeddingPalette_in_finite_ambient b hLoc hr H.subtype K fun c => by
    obtain ⟨g, hg, palette, hp, hpalette⟩ := hK c
    exact ⟨g, hg, palette, hp, fun p =>
      hpalette (b.comp p) (Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩)⟩

/-- Actual unlabelled copies of a first-order structure are precisely the
substructure ranges of embeddings. -/
def FirstOrderCopy (L : Language) (A B : Type*) [L.Structure A] [L.Structure B] :=
  Set.range (fun p : A ↪[L] B => p.toHom.range)

namespace FirstOrderCopy

/-- The unlabelled copy determined by one embedding. -/
def ofEmbedding (p : A ↪[L] B) : FirstOrderCopy L A B :=
  ⟨p.toHom.range, ⟨p, rfl⟩⟩

variable {D : Type*} [L.Structure D]

/-- Transport an unlabelled copy through an ambient embedding. -/
def map (f : B ↪[L] D) (p : FirstOrderCopy L A B) : FirstOrderCopy L A D := by
  refine ⟨p.val.map f.toHom, ?_⟩
  obtain ⟨q, hq⟩ := p.property
  refine ⟨f.comp q, ?_⟩
  change (f.toHom.comp q.toHom).range = p.val.map f.toHom
  rw [Language.Hom.range_comp]
  exact congrArg (Language.Substructure.map f.toHom) hq

omit [Finite A] in
@[simp] theorem map_ofEmbedding (f : B ↪[L] D) (p : A ↪[L] B) :
    map f (ofEmbedding p) = ofEmbedding (f.comp p) := by
  apply Subtype.ext
  exact (Language.Hom.range_comp p.toHom f.toHom).symm

end FirstOrderCopy

omit [Finite A] in
/-- A uniform bound on embedding palettes bounds palettes on unlabelled
copies, by ignoring the labelling of each embedding. -/
theorem firstOrderFiniteCopyDegree_of_embeddingDegree
    (h : ∃ d : ℕ, ∀ (B : Type uM) [L.Structure B] [Finite B]
      (_ : B ↪[L] M) (r : ℕ), 0 < r →
      ∃ C : L.Substructure M, Finite C ∧
        ∀ c : (A ↪[L] C) → Fin r,
          ∃ f : B ↪[L] C, ∃ palette : Finset (Fin r), palette.card ≤ d ∧
            ∀ p : A ↪[L] B, c (f.comp p) ∈ palette) :
    ∃ d : ℕ, ∀ (B : Type uM) [L.Structure B] [Finite B]
      (_ : B ↪[L] M) (r : ℕ), 0 < r →
      ∃ C : L.Substructure M, Finite C ∧
        ∀ c : FirstOrderCopy L A C → Fin r,
          ∃ f : B ↪[L] C, ∃ palette : Finset (Fin r), palette.card ≤ d ∧
            ∀ p : FirstOrderCopy L A B, c (FirstOrderCopy.map f p) ∈ palette := by
  obtain ⟨d, hd⟩ := h
  refine ⟨d, fun B _ _ b r hr => ?_⟩
  obtain ⟨C, hfC, hC⟩ := hd B b r hr
  refine ⟨C, hfC, fun c => ?_⟩
  obtain ⟨f, palette, hp, hpalette⟩ := hC (fun q => c (FirstOrderCopy.ofEmbedding q))
  refine ⟨f, palette, hp, fun p => ?_⟩
  obtain ⟨q, hq⟩ := p.property
  have heq : FirstOrderCopy.ofEmbedding q = p := Subtype.ext hq
  rw [← heq, FirstOrderCopy.map_ofEmbedding]
  exact hpalette q

/-- In the finite age of the locally finite ultrahomogeneous structure,
the existence of a co-precompact extremely amenable subgroup gives a
finite copy Ramsey degree. The source and target may have nontrivial
automorphisms since the colours depend only on their embedded ranges. -/
theorem firstOrderFiniteCopyDegree_of_coprecompactExtremelyAmenable
    (hM : L.IsUltrahomogeneous M) (e : A ↪[L] M)
    (hLoc : ∀ s : Finset M, Finite (Language.Substructure.closure L (s : Set M)))
    (H : Subgroup (FirstOrderAut L M))
    (hH : CoPrecompact (FirstOrderAut L M) H)
    (hfixed : CompactFlowFixedPoint.{uA, uM} H) :
    ∃ d : ℕ, ∀ (B : Type uM) [L.Structure B] [Finite B]
      (_ : B ↪[L] M) (r : ℕ), 0 < r →
      ∃ C : L.Substructure M, Finite C ∧
        ∀ c : FirstOrderCopy L A C → Fin r,
          ∃ f : B ↪[L] C, ∃ palette : Finset (Fin r), palette.card ≤ d ∧
            ∀ p : FirstOrderCopy L A B, c (FirstOrderCopy.map f p) ∈ palette := by
  exact firstOrderFiniteCopyDegree_of_embeddingDegree
    (firstOrderFiniteEmbeddingDegree_of_coprecompactExtremelyAmenable hM e hLoc H hH hfixed)

/-- A continuous homomorphism with dense range transfers extreme
amenability to its codomain. -/
theorem CompactFlowFixedPoint.of_denseRange
    {G K : Type*} [Group G] [Group K] [TopologicalSpace G] [TopologicalSpace K]
    (f : K →* G) (hf : Continuous f) (hDense : DenseRange f)
    (hK : CompactFlowFixedPoint.{uA, uM} K) : CompactFlowFixedPoint.{uA, uM} G := by
  intro Y _ _ _ _ _ _
  let : MulAction K Y := MulAction.compHom Y f
  let : ContinuousSMul K Y := MulAction.continuousSMul_compHom hf
  obtain ⟨y, hy⟩ := hK Y
  have hc : IsClosed {g : G | g • y = y} :=
    isClosed_eq (continuous_id.smul continuous_const) continuous_const
  have hf' : ∀ g ∈ Set.range f, g • y = y := by
    rintro g ⟨k, rfl⟩
    exact hy k
  exact ⟨y, fun g => hDense.induction hf' hc g⟩

/-- Extreme amenability passes from a subgroup of a topological group to
its topological closure, with the inherited subspace topology. -/
theorem CompactFlowFixedPoint.topologicalClosure
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (H : Subgroup G) (hH : CompactFlowFixedPoint.{uA, uM} H) :
    CompactFlowFixedPoint.{uA, uM} H.topologicalClosure := by
  let f := Subgroup.inclusion H.le_topologicalClosure
  have hf : Continuous f := continuous_inclusion H.le_topologicalClosure
  have hd : DenseRange f := (denseRange_inclusion_iff H.le_topologicalClosure).mpr
    (by rw [Subgroup.topologicalClosure_coe])
  exact CompactFlowFixedPoint.of_denseRange f hf hd hH

end SuccessorTree.NonPrecompact
