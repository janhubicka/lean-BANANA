import BANANA.NonPrecompact.BananaCopyRanges
import Mathlib.Data.Fintype.OfMap
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Finite residue palettes on unlabelled BANANA copies

The set of line-pair colours inside an unlabelled copy is independent
of a choice of basis or an enumeration of the source. Its cardinality
is bounded by the number of line pairs of the source itself.

The small union lemma at the end is the counting step in the direct
proof that all two-sided BANANA sources have infinite *copy* Ramsey
degree. It avoids choosing representatives for the automorphism
orbits of embeddings.
-/

namespace SuccessorTree.NonPrecompact

/-- A line-pair type is finite because it embeds into the product
of its two finite coordinate spaces. -/
noncomputable instance bananaLinePairFintype
    {l r : ℕ} (A : BananaMatrixStructure l r) (b : F2) :
    Fintype (BananaLinePairCopy A b) := by
  classical
  let embedding : BananaLinePairCopy A b →
      (Fin l → F2) × (Fin r → F2) :=
    fun P => (P.left, P.right)
  have hinj : Function.Injective embedding := by
    intro P Q h
    exact BananaLinePairCopy.eq_of_vectors P Q
      (congrArg Prod.fst h) (congrArg Prod.snd h)
  exact Fintype.ofInjective embedding hinj

/-- The colours of all line pairs contained in an unlabelled copy.
This is a subset of the ambient finite colour set, not a colour of
an arbitrarily selected parametrisation of the copy. -/
noncomputable def BananaCopyRanges.linePairPalette
    {l r lC rC numColours : ℕ}
    {A : BananaMatrixStructure l r}
    {C : BananaMatrixStructure lC rC}
    {b : F2}
    (D : BananaCopyRanges A C)
    (colouring : BananaLinePairCopy C b → Fin numColours) :
    Finset (Fin numColours) := by
  classical
  exact Finset.univ.filter
    (fun c => ∃ P : BananaLinePairCopy C b,
      P.InCopy D ∧ colouring P = c)

/-- Membership in the palette means occurrence on some
line-pair copy inside the given unlabelled copy. -/
theorem BananaCopyRanges.mem_linePairPalette_iff
    {l r lC rC numColours : ℕ}
    {A : BananaMatrixStructure l r}
    {C : BananaMatrixStructure lC rC}
    {b : F2}
    (D : BananaCopyRanges A C)
    (colouring : BananaLinePairCopy C b → Fin numColours)
    (c : Fin numColours) :
    c ∈ D.linePairPalette colouring ↔
      ∃ P : BananaLinePairCopy C b,
        P.InCopy D ∧ colouring P = c := by
  classical
  simp [BananaCopyRanges.linePairPalette]

/-- Every contained line pair contributes its colour to the palette. -/
theorem BananaCopyRanges.colour_mem_linePairPalette
    {l r lC rC numColours : ℕ}
    {A : BananaMatrixStructure l r}
    {C : BananaMatrixStructure lC rC}
    {b : F2}
    (D : BananaCopyRanges A C)
    (colouring : BananaLinePairCopy C b → Fin numColours)
    (P : BananaLinePairCopy C b)
    (h : P.InCopy D) :
    colouring P ∈ D.linePairPalette colouring := by
  apply (D.mem_linePairPalette_iff colouring _).2
  exact ⟨P, h, rfl⟩

/-- Once a source embedding has been selected, the palette of the
unlabelled image is exactly the image of the source's finite set of
line pairs under its induced colouring. -/
theorem BananaMatrixEmbedding.linePairPalette_copyRanges
    {l r lC rC numColours : ℕ}
    {A : BananaMatrixStructure l r}
    {C : BananaMatrixStructure lC rC}
    {b : F2}
    (e : BananaMatrixEmbedding A C)
    (colouring : BananaLinePairCopy C b → Fin numColours) :
    e.copyRanges.linePairPalette colouring =
      (Finset.univ : Finset (BananaLinePairCopy A b)).image
        (fun P => colouring (e.mapLinePairCopy P)) := by
  classical
  ext c
  rw [BananaCopyRanges.mem_linePairPalette_iff]
  constructor
  · rintro ⟨P, hinside, hc⟩
    obtain ⟨Q, hQ⟩ := e.exists_linePair_preimage P hinside
    apply Finset.mem_image.mpr
    refine ⟨Q, Finset.mem_univ _, ?_⟩
    simpa only [hQ] using hc
  · intro hc
    obtain ⟨Q, _, hQ⟩ := Finset.mem_image.mp hc
    have hinside : (e.mapLinePairCopy Q).InCopy e.copyRanges := by
      classical
      constructor
      · change e.left Q.left ∈ Finset.univ.image e.left
        exact Finset.mem_image.mpr
          ⟨Q.left, Finset.mem_univ _, rfl⟩
      · change e.right Q.right ∈ Finset.univ.image e.right
        exact Finset.mem_image.mpr
          ⟨Q.right, Finset.mem_univ _, rfl⟩
    exact ⟨e.mapLinePairCopy Q, hinside, hQ⟩

/-- The palette of any unlabelled source copy has at most as many
colours as there are line-pair copies in the source itself. -/
theorem BananaCopyRanges.card_linePairPalette_le_source
    {l r lC rC numColours : ℕ}
    {A : BananaMatrixStructure l r}
    {C : BananaMatrixStructure lC rC}
    {b : F2}
    (D : BananaCopyRanges A C)
    (colouring : BananaLinePairCopy C b → Fin numColours) :
    (D.linePairPalette colouring).card ≤
      Fintype.card (BananaLinePairCopy A b) := by
  classical
  obtain ⟨e, hl, hr⟩ := D.property
  have hD : D = e.copyRanges := by
    apply Subtype.ext
    exact Prod.ext hl hr
  subst D
  rw [e.linePairPalette_copyRanges colouring]
  simpa only [Finset.card_univ] using
    (Finset.card_image_le :
      ((Finset.univ : Finset (BananaLinePairCopy A b)).image
        (fun P => colouring (e.mapLinePairCopy P))).card ≤
        (Finset.univ : Finset (BananaLinePairCopy A b)).card)

/-- The familiar finite-union estimate in the exact form needed
for copy-colour palettes. -/
theorem card_biUnion_palette_le
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α))
    (s : ℕ)
    (hbound : ∀ colours ∈ family, colours.card ≤ s) :
    (family.biUnion id).card ≤ family.card * s := by
  classical
  calc
    (family.biUnion id).card ≤
        ∑ colours ∈ family, colours.card := Finset.card_biUnion_le
    _ ≤ ∑ _colours ∈ family, s := by
      apply Finset.sum_le_sum
      intro colours hmem
      exact hbound colours hmem
    _ = family.card * s := by simp

end SuccessorTree.NonPrecompact
