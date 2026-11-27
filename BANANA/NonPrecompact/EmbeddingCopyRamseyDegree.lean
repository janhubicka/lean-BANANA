import BANANA.CopyRamsey

/-!
# Embedding and copy Ramsey degrees

For a fixed source, each copy has as many embeddings onto it as the source
has automorphisms. The proof only needs a uniform enumeration of each fibre
of the range map and the fact that postcomposition maps each fibre onto
the corresponding fibre in the larger ambient structure.
-/

namespace SuccessorTree.FiniteCopySystem

variable {S : FiniteCopySystem} {A : S.Obj} {m : ℕ}

attribute [local instance] FiniteCopySystem.copyFintype

/-- Each copy of the fixed source has a uniformly sized fibre of embeddings. -/
structure UniformEmbeddingFibres (S : FiniteCopySystem) (A : S.Obj) (m : ℕ) where
  index : ∀ {B}, (p : S.Copy A B) → {e : S.Emb A B // S.range e = p} ≃ Fin m
  postcomp_surjective : ∀ {B C} (f : S.Emb B C) (p : S.Copy A B),
    Function.Surjective (fun e : {e : S.Emb A B // S.range e = p} =>
      (⟨S.compEmb e.val f, (S.range_comp _ _).trans (congrArg (S.mapCopy f) e.property)⟩ :
        {e : S.Emb A C // S.range e = S.mapCopy f p}))

/-- Colours on embeddings of the source into the image of a target embedding. -/
noncomputable def embeddingColoursInside {A B C : S.Obj} {r : ℕ}
    (colouring : S.Emb A C → Fin r) (f : S.Emb B C) : Finset (Fin r) := by
  classical
  exact Finset.univ.filter (fun c => ∃ e : S.Emb A B, colouring (S.compEmb e f) = c)

@[simp] theorem mem_embeddingColoursInside {A B C : S.Obj} {r : ℕ}
    (colouring : S.Emb A C → Fin r) (f : S.Emb B C) (c : Fin r) :
    c ∈ embeddingColoursInside colouring f ↔
      ∃ e : S.Emb A B, colouring (S.compEmb e f) = c := by
  classical
  simp [embeddingColoursInside]

/-- A finite upper bound on the embedding Ramsey degree, with the same
target and colour quantifiers as the copy Ramsey degree. -/
def EmbeddingRamseyDegreeLE (S : FiniteCopySystem) (A : S.Obj) (t : ℕ) : Prop :=
  ∀ (B : S.Obj) (r : ℕ), 0 < r →
    ∃ C : S.Obj, ∀ colouring : S.Emb A C → Fin r,
      ∃ f : S.Emb B C, (embeddingColoursInside colouring f).card ≤ t

/-- A copy degree bound is positive, by testing the source as its own target. -/
theorem copyRamseyDegreeLE_pos {t : ℕ} (h : S.CopyRamseyDegreeLE A t) : 0 < t := by
  classical
  obtain ⟨C, hC⟩ := h A 1 Nat.one_pos
  let colour : S.Copy A C → Fin 1 := fun _ => 0
  obtain ⟨f, hf⟩ := hC colour
  have hmem : (0 : Fin 1) ∈ S.coloursInside colour f :=
    Finset.mem_image.mpr ⟨S.range (S.idEmb A), Finset.mem_univ _, rfl⟩
  exact (Finset.card_pos.mpr ⟨0, hmem⟩).trans_le hf

namespace UniformEmbeddingFibres

variable (H : UniformEmbeddingFibres S A m)
include H

/-- The uniform fibre size is positive, since the identity embeds the
source onto its own range. -/
theorem size_pos : 0 < m :=
  (Nat.zero_le _).trans_lt (H.index (S.range (S.idEmb A)) ⟨S.idEmb A, rfl⟩).isLt

private theorem index_eq_of_range {B : S.Obj} (e : S.Emb A B) {p : S.Copy A B}
    (hp : S.range e = p) :
    H.index (S.range e) ⟨e, rfl⟩ = H.index p ⟨e, hp⟩ := by
  subst p
  rfl

/-- Colour a copy by the tuple of colours on all embeddings onto it. -/
theorem embeddingRamseyDegreeLE_of_copyRamseyDegreeLE {t : ℕ}
    (h : S.CopyRamseyDegreeLE A t) : S.EmbeddingRamseyDegreeLE A (m * t) := by
  classical
  intro B r hr
  let Palette := Fin m → Fin r
  let n := Fintype.card Palette
  let code : Palette ≃ Fin n := Fintype.equivFin _
  have hn : 0 < n := Fintype.card_pos_iff.mpr ⟨fun _ => ⟨0, hr⟩⟩
  obtain ⟨C, hC⟩ := h B n hn
  refine ⟨C, fun colouring => ?_⟩
  let colours : S.Copy A C → Palette :=
    fun p i => colouring ((H.index p).symm i).val
  let copyColour : S.Copy A C → Fin n := fun p => code (colours p)
  obtain ⟨f, hf⟩ := hC copyColour
  let paletteColours (z : Fin n) := Finset.univ.image (code.symm z)
  have hsize (z : Fin n) : (paletteColours z).card ≤ m := by
    exact Finset.card_image_le.trans (by simp)
  refine ⟨f, ?_⟩
  have hsub : embeddingColoursInside colouring f ⊆
      (S.coloursInside copyColour f).biUnion paletteColours := by
    intro c hc
    obtain ⟨e, rfl⟩ := (mem_embeddingColoursInside _ _ _).mp hc
    let p := S.range e
    let j : {e' : S.Emb A C // S.range e' = S.mapCopy f p} :=
      ⟨S.compEmb e f, S.range_comp _ _⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨copyColour (S.mapCopy f p), Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨H.index _ j, Finset.mem_univ _, ?_⟩
    simp [copyColour, colours, j]
  calc
    (embeddingColoursInside colouring f).card ≤
        ((S.coloursInside copyColour f).biUnion paletteColours).card := Finset.card_le_card hsub
    _ ≤ (S.coloursInside copyColour f).card * m :=
      Finset.card_biUnion_le_card_mul _ _ _ (fun z _ => hsize z)
    _ ≤ m * t := by
      rw [Nat.mul_comm m t]
      exact Nat.mul_le_mul_right _ hf

/-- Pair each copy colour with the index of an embedding onto its range.
Every copy in a target then contributes all the colours with its copy colour
as first coordinate. -/
theorem copyRamseyDegreeLE_div_of_embeddingRamseyDegreeLE {t : ℕ}
    (h : S.EmbeddingRamseyDegreeLE A t) : S.CopyRamseyDegreeLE A (t / m) := by
  classical
  intro B r hr
  let Palette := Fin r × Fin m
  let n := Fintype.card Palette
  let code : Palette ≃ Fin n := Fintype.equivFin _
  have hn : 0 < n := Fintype.card_pos_iff.mpr ⟨⟨⟨0, hr⟩, ⟨0, H.size_pos⟩⟩⟩
  obtain ⟨C, hC⟩ := h B n hn
  refine ⟨C, fun colouring => ?_⟩
  let embeddingColour : S.Emb A C → Fin n :=
    fun e => code (colouring (S.range e), H.index (S.range e) ⟨e, rfl⟩)
  obtain ⟨f, hf⟩ := hC embeddingColour
  let targetColours := S.coloursInside colouring f ×ˢ (Finset.univ : Finset (Fin m))
  have hsub : targetColours.image code ⊆ embeddingColoursInside embeddingColour f := by
    intro c hc
    obtain ⟨⟨c₀, i⟩, hc₀, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨p, -, hp⟩ := Finset.mem_image.mp (Finset.mem_product.mp hc₀).1
    obtain ⟨e, he⟩ := H.postcomp_surjective f p ((H.index (S.mapCopy f p)).symm i)
    have hcomp : S.range (S.compEmb e.val f) = S.mapCopy f p :=
      (S.range_comp _ _).trans (congrArg (S.mapCopy f) e.property)
    have hindex : H.index (S.range (S.compEmb e.val f)) ⟨S.compEmb e.val f, rfl⟩ = i := by
      rw [H.index_eq_of_range _ hcomp]
      exact (congrArg (H.index (S.mapCopy f p)) he).trans
        ((H.index (S.mapCopy f p)).apply_symm_apply i)
    apply (mem_embeddingColoursInside _ _ _).mpr
    refine ⟨e.val, ?_⟩
    change code (colouring (S.range (S.compEmb e.val f)), _) = code (c₀, i)
    rw [hindex]
    exact congrArg (fun c => code (c, i)) ((congrArg colouring hcomp).trans hp)
  have hcard : (targetColours.image code).card = (S.coloursInside colouring f).card * m := by
    rw [Finset.card_image_of_injective _ code.injective]
    simpa only [targetColours, Finset.card_univ, Fintype.card_fin] using
      Finset.card_product (S.coloursInside colouring f) (Finset.univ : Finset (Fin m))
  refine ⟨f, (Nat.le_div_iff_mul_le H.size_pos).mpr ?_⟩
  calc
    (S.coloursInside colouring f).card * m = (targetColours.image code).card := hcard.symm
    _ ≤ (embeddingColoursInside embeddingColour f).card := Finset.card_le_card hsub
    _ ≤ t := hf

/-- Exact finite-bound formulation of the relationship between embedding and
copy Ramsey degrees. It also determines when either degree is infinite. -/
theorem embeddingRamseyDegreeLE_iff_copyRamseyDegreeLE_div {t : ℕ} :
    S.EmbeddingRamseyDegreeLE A t ↔ S.CopyRamseyDegreeLE A (t / m) := by
  refine ⟨H.copyRamseyDegreeLE_div_of_embeddingRamseyDegreeLE, fun h B r hr => ?_⟩
  obtain ⟨C, hC⟩ := H.embeddingRamseyDegreeLE_of_copyRamseyDegreeLE h B r hr
  refine ⟨C, fun colouring => ?_⟩
  obtain ⟨f, hf⟩ := hC colouring
  exact ⟨f, hf.trans (by simpa only [Nat.mul_comm] using Nat.div_mul_le_self t m)⟩

/-- An embedding bound multiplied by the fibre size is equivalent to the
unscaled copy bound. This includes arbitrary finite copy bounds, not just
the least one. -/
theorem embeddingRamseyDegreeLE_mul_iff {t : ℕ} :
    S.EmbeddingRamseyDegreeLE A (m * t) ↔ S.CopyRamseyDegreeLE A t := by
  rw [H.embeddingRamseyDegreeLE_iff_copyRamseyDegreeLE_div, Nat.mul_div_cancel_left _ H.size_pos]

/-- The exact finite embedding Ramsey degree is the copy degree multiplied
by the number of embeddings onto each copy. -/
theorem isLeast_embeddingRamseyDegree {t : ℕ}
    (h : IsLeast {d : ℕ | S.CopyRamseyDegreeLE A d} t) :
    IsLeast {d : ℕ | S.EmbeddingRamseyDegreeLE A d} (m * t) := by
  refine ⟨H.embeddingRamseyDegreeLE_of_copyRamseyDegreeLE h.1, ?_⟩
  intro d hd
  have hle : t ≤ d / m := h.2 (H.copyRamseyDegreeLE_div_of_embeddingRamseyDegreeLE hd)
  exact (Nat.mul_comm t m) ▸ (Nat.le_div_iff_mul_le H.size_pos).mp hle

/-- The two degrees are infinite for exactly the same source structures. -/
theorem embeddingRamseyDegree_infinite_iff :
    (∀ t : ℕ, ¬ S.EmbeddingRamseyDegreeLE A t) ↔
      (∀ t : ℕ, ¬ S.CopyRamseyDegreeLE A t) := by
  refine ⟨fun h t hc => h _ ((H.embeddingRamseyDegreeLE_mul_iff).mpr hc), ?_⟩
  exact fun h _ he => h _ ((H.embeddingRamseyDegreeLE_iff_copyRamseyDegreeLE_div).mp he)

end UniformEmbeddingFibres

end SuccessorTree.FiniteCopySystem
