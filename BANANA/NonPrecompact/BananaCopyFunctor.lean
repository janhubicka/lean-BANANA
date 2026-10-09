import BANANA.NonPrecompact.BananaOneSidedSubspaceEquiv

/-!
# Functoriality of unlabelled BANANA copies and their line-pair palettes

A copy is recorded by its two image subspaces (as finite sets of vectors),
rather than by a chosen embedding of its source. The following lemmas
make that presentation functorial under BANANA embeddings.

They also show that a line-pair contained in the image of a copy has
a preimage line-pair in that copy, and that the finite residue palette
is preserved exactly under pullback of an ambient colouring. These
facts are useful in the circulation degree classification and avoid
any choice of representatives of a source automorphism orbit.

This file is staged pending local Lean compilation and axiom checks.
-/

namespace SuccessorTree.NonPrecompact

/-- Mapping an unlabelled copy through two ambient embeddings is the
same as mapping it through their composite. -/
theorem BananaCopyRanges.map_comp
    {l r lB rB lC rC lD rD : ℕ}
    {A : BananaMatrixStructure l r}
    {B : BananaMatrixStructure lB rB}
    {C : BananaMatrixStructure lC rC}
    {D : BananaMatrixStructure lD rD}
    (P : BananaCopyRanges A B)
    (f : BananaMatrixEmbedding B C)
    (g : BananaMatrixEmbedding C D) :
    (P.map f).map g = P.map (BananaMatrixEmbedding.comp g f) := by
  classical
  apply Subtype.ext
  apply Prod.ext
  · change (P.1.1.image f.left).image g.left =
        P.1.1.image ((BananaMatrixEmbedding.comp g f).left)
    rw [Finset.image_image]
    rfl
  · change (P.1.2.image f.right).image g.right =
        P.1.2.image ((BananaMatrixEmbedding.comp g f).right)
    rw [Finset.image_image]
    rfl

/-- The identity embedding fixes every unlabelled copy. -/
theorem BananaCopyRanges.map_identity
    {l r lB rB : ℕ}
    {A : BananaMatrixStructure l r}
    {B : BananaMatrixStructure lB rB}
    (P : BananaCopyRanges A B) :
    P.map (BananaMatrixEmbedding.identity B) = P := by
  classical
  apply Subtype.ext
  apply Prod.ext
  · change P.1.1.image (LinearMap.id : (Fin lB → F2) →ₗ[F2] _) =
        P.1.1
    simp
  · change P.1.2.image (LinearMap.id : (Fin rB → F2) →ₗ[F2] _) =
        P.1.2
    simp

/-- An ambient embedding reflects equality of unlabelled copies.
The source automorphisms have already been forgotten by the
image-range representation. -/
theorem BananaCopyRanges.map_injective
    {l r lB rB lC rC : ℕ}
    {A : BananaMatrixStructure l r}
    {B : BananaMatrixStructure lB rB}
    {C : BananaMatrixStructure lC rC}
    (f : BananaMatrixEmbedding B C) :
    Function.Injective (fun P : BananaCopyRanges A B => P.map f) := by
  classical
  intro P Q heq
  have hleft : P.1.1.image f.left = Q.1.1.image f.left := by
    exact congrArg Prod.fst (congrArg Subtype.val heq)
  have hright : P.1.2.image f.right = Q.1.2.image f.right := by
    exact congrArg Prod.snd (congrArg Subtype.val heq)
  apply Subtype.ext
  apply Prod.ext
  · ext x
    constructor
    · intro hx
      have hmem : f.left x ∈ Q.1.1.image f.left := by
        rw [← hleft]
        exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hmem
      have hyx : y = x := f.left_injective hxy
      simpa [hyx] using hy
    · intro hx
      have hmem : f.left x ∈ P.1.1.image f.left := by
        rw [hleft]
        exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hmem
      have hyx : y = x := f.left_injective hxy
      simpa [hyx] using hy
  · ext y
    constructor
    · intro hy
      have hmem : f.right y ∈ Q.1.2.image f.right := by
        rw [← hright]
        exact Finset.mem_image.mpr ⟨y, hy, rfl⟩
      obtain ⟨z, hz, hyz⟩ := Finset.mem_image.mp hmem
      have hzy : z = y := f.right_injective hyz
      simpa [hzy] using hz
    · intro hy
      have hmem : f.right y ∈ P.1.2.image f.right := by
        rw [hright]
        exact Finset.mem_image.mpr ⟨y, hy, rfl⟩
      obtain ⟨z, hz, hyz⟩ := Finset.mem_image.mp hmem
      have hzy : z = y := f.right_injective hyz
      simpa [hzy] using hz

/-- A line-pair contained in an ambient image of an unlabelled copy
comes from a line-pair contained in the original copy. -/
theorem BananaLinePairCopy.exists_preimage_of_in_mapped_copy
    {l r lB rB lC rC : ℕ}
    {A : BananaMatrixStructure l r}
    {B : BananaMatrixStructure lB rB}
    {C : BananaMatrixStructure lC rC}
    {b : F2}
    (f : BananaMatrixEmbedding B C)
    (D : BananaCopyRanges A B)
    (P : BananaLinePairCopy C b)
    (hP : P.InCopy (D.map f)) :
    ∃ Q : BananaLinePairCopy B b,
      Q.InCopy D ∧ f.mapLinePairCopy Q = P := by
  classical
  have hleft : P.left ∈ D.1.1.image f.left := hP.1
  have hright : P.right ∈ D.1.2.image f.right := hP.2
  obtain ⟨x, hxmem, hfx⟩ := Finset.mem_image.mp hleft
  obtain ⟨y, hymem, hfy⟩ := Finset.mem_image.mp hright
  have hx : x ≠ 0 := by
    intro heq
    apply P.left_ne_zero
    calc
      P.left = f.left x := hfx.symm
      _ = 0 := by simp [heq]
  have hy : y ≠ 0 := by
    intro heq
    apply P.right_ne_zero
    calc
      P.right = f.right y := hfy.symm
      _ = 0 := by simp [heq]
  have hp : B.eval x y = b := by
    calc
      B.eval x y = C.eval (f.left x) (f.right y) :=
        (f.pairing_apply x y).symm
      _ = b := by rw [hfx, hfy]; exact P.pairing
  let Q : BananaLinePairCopy B b := ⟨x, y, hx, hy, hp⟩
  refine ⟨Q, ⟨hxmem, hymem⟩, ?_⟩
  apply BananaLinePairCopy.eq_of_vectors
  · exact hfx
  · exact hfy

/-- The palette of an unlabelled copy in the image of an embedding is
exactly the palette in the source for the pulled-back line-pair
colouring. In particular, no source representatives are chosen. -/
theorem BananaCopyRanges.linePairPalette_map
    {l r lB rB lC rC numColours : ℕ}
    {A : BananaMatrixStructure l r}
    {B : BananaMatrixStructure lB rB}
    {C : BananaMatrixStructure lC rC}
    {b : F2}
    (D : BananaCopyRanges A B)
    (f : BananaMatrixEmbedding B C)
    (colouring : BananaLinePairCopy C b → Fin numColours) :
    (D.map f).linePairPalette colouring =
      D.linePairPalette
        (fun P => colouring (f.mapLinePairCopy P)) := by
  classical
  ext c
  rw [(D.map f).mem_linePairPalette_iff colouring c,
      D.mem_linePairPalette_iff
        (fun P => colouring (f.mapLinePairCopy P)) c]
  constructor
  · rintro ⟨P, hP, hcolour⟩
    obtain ⟨Q, hQ, hmap⟩ :=
      BananaLinePairCopy.exists_preimage_of_in_mapped_copy f D P hP
    refine ⟨Q, hQ, ?_⟩
    simpa only [hmap] using hcolour
  · rintro ⟨Q, hQ, hcolour⟩
    exact ⟨f.mapLinePairCopy Q, hQ.map f, hcolour⟩

end SuccessorTree.NonPrecompact
