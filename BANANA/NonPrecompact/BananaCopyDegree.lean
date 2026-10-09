import BANANA.NonPrecompact.BananaCopyPalette
import Mathlib.Data.Fintype.EquivFin

/-!
# Infinite *copy* Ramsey degree for two-sided BANANA structures

This is the direct set-valued colouring argument suggested by the
circulation manuscript's validation TODO. Unlike the preceding
embedding-colouring obstruction, the colour of a copy here depends
only on its two underlying ranges and is therefore independent of
the choice of a source isomorphism or of source automorphisms.

For a chosen line-pair substructure `A_b` of `A`, let `s` be the
number of line-pair copies of `A_b` contained in `A`. Colour each
unlabelled copy of `A` by the set of its line-pair residue colours.
This set has at most `s` elements. The persistent-colouring theorem
and the prescribed line-pair extension lemma show that a sufficiently
large perfect target forces all `2^k` residue colours to occur among
its copies. At most `t` set-colours would cover at most `t*s` residues.
Choosing `k = t*s` contradicts `t*s < 2^k`.

The source is represented as a pair of finite-dimensional F₂ spaces
with a bilinear pairing, exactly as in the circulating BANANA paper.
-/

namespace SuccessorTree.NonPrecompact

/-- Copy Ramsey degree at most `t`, with colourings of *unlabelled
source copies* rather than colourings of embeddings. Copies are
identified by the images of their two vector-space sorts. -/
def BananaMatrixStructure.copyRamseyDegreeLE
    {l r : ℕ} (A : BananaMatrixStructure l r) (t : ℕ) : Prop :=
  ∀ (lB rB : ℕ) (B : BananaMatrixStructure lB rB)
      (numColours : ℕ), 0 < numColours →
    ∃ (lC rC : ℕ) (C : BananaMatrixStructure lC rC),
      ∀ colouring : BananaCopyRanges A C → Fin numColours,
        ∃ f : BananaMatrixEmbedding B C,
          ∃ colours : Finset (Fin numColours),
            colours.card ≤ t ∧
            ∀ D : BananaCopyRanges A B,
              colouring (D.map f) ∈ colours

/-- A line-pair substructure gives infinite copy Ramsey degree for
the entire source, directly and without the general
amalgamation-class degree-propagation theorem. -/
theorem BananaMatrixStructure.not_copyRamseyDegreeLE_of_linePair
    {l r : ℕ} (A : BananaMatrixStructure l r)
    {b : F2}
    (i : BananaMatrixEmbedding (linePairSource b) A)
    (t : ℕ) :
    ¬ A.copyRamseyDegreeLE t := by
  classical
  intro hdegree
  let s : ℕ := Fintype.card (BananaLinePairCopy A b)
  let k : ℕ := t * s
  let q : ℕ := (2 ^ (k + 1) - 1) + 1
  let n : ℕ := (l + r) + q
  let numColours : ℕ :=
    Fintype.card (Finset (Fin (2 ^ k)))
  let encode :
      Finset (Fin (2 ^ k)) ≃ Fin numColours :=
    Fintype.equivFin (Finset (Fin (2 ^ k)))
  have hnumColours : 0 < numColours := by
    exact Fintype.card_pos_iff.mpr
      ⟨(∅ : Finset (Fin (2 ^ k)))⟩
  obtain ⟨lC, rC, C, hC⟩ :=
    hdegree n n (perfectBanana n) numColours hnumColours
  obtain ⟨lineColour, hpersistent⟩ :=
    exists_completionResiduePersistentColouring C k b
  let colouring : BananaCopyRanges A C → Fin numColours :=
    fun D => encode (D.linePairPalette lineColour)
  obtain ⟨f, usedColours, husedCard, hused⟩ := hC colouring

  let j :
      BananaMatrixEmbedding (perfectBanana q) (perfectBanana n) := by
    have hn : q + (l + r) = n := by
      dsimp [n]
      omega
    exact hn ▸ (BananaMatrixStructure.standardPerfectBlockEmbedding q (l + r))

  /- Distinct colours of unlabelled A-copies are finite residue
     palettes, independent of the choice of embeddings of A. -/
  let family : Finset (Finset (Fin (2 ^ k))) :=
    (Finset.univ : Finset (BananaCopyRanges A (perfectBanana n))).image
      (fun D => (D.map f).linePairPalette lineColour)

  have family_subset :
      family ⊆ usedColours.image encode.symm := by
    intro S hS
    obtain ⟨D, _, hD⟩ := Finset.mem_image.mp hS
    refine Finset.mem_image.mpr
      ⟨colouring (D.map f), hused D, ?_⟩
    simpa only [colouring, Equiv.symm_apply_apply] using hD

  have family_card_le : family.card ≤ t := by
    calc
      family.card ≤ (usedColours.image encode.symm).card :=
        Finset.card_le_card family_subset
      _ ≤ usedColours.card := Finset.card_image_le
      _ ≤ t := husedCard

  have family_palette_bound :
      ∀ S ∈ family, S.card ≤ s := by
    intro S hS
    obtain ⟨D, _, hD⟩ := Finset.mem_image.mp hS
    rw [← hD]
    exact (D.map f).card_linePairPalette_le_source lineColour

  /- The fixed completion colouring sees every residue inside
     every embedded perfect q-block. Any such line pair in B_n
     extends to an A-copy inside B_n by homogeneity. -/
  have full_palette :
      (Finset.univ : Finset (Fin (2 ^ k))) ⊆
        family.biUnion id := by
    intro c _
    obtain ⟨P, hP⟩ :=
      hpersistent (BananaMatrixEmbedding.comp f j) c
    let P' : BananaLinePairCopy (perfectBanana n) b :=
      j.mapLinePairCopy P
    obtain ⟨e, he⟩ :=
      A.exists_extend_linePairCopy i q P'
    let D : BananaCopyRanges A (perfectBanana n) := e.copyRanges
    have hcontained : P'.InCopy D := by
      rw [← he]
      exact e.toLinePairCopy_in_copyRanges i
    have hcontainedInC :
        (f.mapLinePairCopy P').InCopy (D.map f) :=
      hcontained.map f
    have hcolour : lineColour (f.mapLinePairCopy P') = c := by
      simpa only [P',
        BananaMatrixEmbedding.mapLinePairCopy_comp] using hP
    have hmem :
        c ∈ (D.map f).linePairPalette lineColour := by
      have hm := (D.map f).colour_mem_linePairPalette
        lineColour (f.mapLinePairCopy P') hcontainedInC
      rw [hcolour] at hm
      exact hm
    exact Finset.mem_biUnion.mpr
      ⟨(D.map f).linePairPalette lineColour,
        Finset.mem_image.mpr ⟨D, Finset.mem_univ _, rfl⟩,
        hmem⟩

  have htooFew : 2 ^ k ≤ t * s := by
    have hcoverCard :
        2 ^ k ≤ (family.biUnion id).card := by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        (Finset.card_le_card full_palette)
    calc
      2 ^ k ≤ (family.biUnion id).card := hcoverCard
      _ ≤ family.card * s :=
        card_biUnion_palette_le family s family_palette_bound
      _ ≤ t * s := Nat.mul_le_mul_right s family_card_le
  have hlarge : t * s < 2 ^ k := by
    change t * s < 2 ^ (t * s)
    exact Nat.lt_two_pow_self (t * s)
  exact (Nat.not_le_of_gt hlarge) htooFew

/-- Every BANANA source admitting a four-element line-pair
substructure has infinite *unlabelled copy* Ramsey degree. -/
theorem BananaMatrixStructure.copyRamseyDegree_infinite_of_linePair
    {l r : ℕ} (A : BananaMatrixStructure l r)
    {b : F2}
    (i : BananaMatrixEmbedding (linePairSource b) A) :
    ∀ t : ℕ, ¬ A.copyRamseyDegreeLE t := by
  intro t
  exact A.not_copyRamseyDegreeLE_of_linePair i t

/-- The two-sided half of the manuscript's complete copy Ramsey
degree classification, stated for all finite BANANA matrices. -/
theorem BananaMatrixStructure.copyRamseyDegree_infinite_of_positive
    {l r : ℕ} (A : BananaMatrixStructure l r)
    (hl : 0 < l) (hr : 0 < r) :
    ∀ t : ℕ, ¬ A.copyRamseyDegreeLE t := by
  obtain ⟨b, ⟨P⟩⟩ := A.exists_linePairCopy_of_positive hl hr
  exact A.copyRamseyDegree_infinite_of_linePair
    P.toSourceEmbedding

end SuccessorTree.NonPrecompact
