import BANANA.NonPrecompact.FirstOrderRamseyExpansion
import BANANA.NonPrecompact.FolkmanFirstOrder
import BANANA.NonPrecompact.FolkmanFirstOrderFraisse
import BANANA.NonPrecompact.FolkmanRamseyExpansionObstruction

/-!
# The relational Ramsey expansion obstruction for Folkman–BANANA

A first-order copy in the product encoding is the Cartesian product of
the two native copy ranges. The native persistent colouring therefore
gives infinite copy Ramsey degree in the actual first-order age.
-/

namespace SuccessorTree.NonPrecompact

open CategoryTheory FirstOrder
open scoped FirstOrder

namespace FolkmanFirstOrder

open FolkmanNativeFiniteModel

private theorem finite_of_mem (B : Bundled.{0} folkmanLanguage.Structure)
    (hB : B ∈ folkmanFirstOrderClass) : Finite B := by
  obtain ⟨A, ⟨e⟩⟩ := hB
  exact Finite.of_injective e e.injective

private noncomputable abbrev copySystem :=
  firstOrderFiniteCopySystem folkmanFirstOrderClass finite_of_mem

private abbrev bundle (A : FolkmanNativeFiniteModel) := folkmanProductBundle A.pairing

private noncomputable def diagonal (q : ℕ) : folkmanFirstOrderClass :=
  ⟨bundle (folkmanNativeDiagonal q), folkmanProductBundle_mem _⟩

private noncomputable def nativeOfCode (B : FolkmanAtomStructure) : FolkmanNativeFiniteModel where
  Left := FolkmanNativeCodeRing B.leftCount
  Right := FolkmanNativeCodeRing B.rightCount
  pairing := folkmanNativeCodeRealisation B

private noncomputable def encode {A B : FolkmanNativeFiniteModel} (g : Embedding A B) :
    bundle A ↪[folkmanLanguage] bundle B :=
  folkmanNativePairingEmbeddingEquiv A.pairing B.pairing g

private noncomputable def decode {A B : FolkmanNativeFiniteModel}
    (g : bundle A ↪[folkmanLanguage] bundle B) : Embedding A B :=
  (folkmanNativePairingEmbeddingEquiv A.pairing B.pairing).symm g

private theorem encode_decode {A B : FolkmanNativeFiniteModel}
    (g : bundle A ↪[folkmanLanguage] bundle B) : encode (decode g) = g :=
  (folkmanNativePairingEmbeddingEquiv A.pairing B.pairing).apply_symm_apply g

private theorem range_encode {A B : FolkmanNativeFiniteModel} (g : Embedding A B) :
    Set.range (encode g) = Set.range g.left ×ˢ Set.range g.right := by
  change Set.range (Prod.map g.left g.right) = _
  exact Set.range_prodMap

private theorem range_decode {A B : FolkmanNativeFiniteModel} {C : folkmanFirstOrderClass}
    (e : C.val ≃[folkmanLanguage] bundle B) (f : bundle A ↪[folkmanLanguage] C.val) :
    e.symm '' (Set.range (decode (e.toEmbedding.comp f)).left ×ˢ
      Set.range (decode (e.toEmbedding.comp f)).right) = Set.range f := by
  rw [← range_encode, encode_decode]
  change _ '' Set.range (e ∘ f) = _
  rw [Set.range_comp, Set.image_image]
  simp only [Language.Equiv.symm_apply_apply, Set.image_id']

private def toRange {A B : FolkmanNativeFiniteModel} {P C : folkmanFirstOrderClass}
    (hP : P.val = bundle A) (e : C.val ≃[folkmanLanguage] bundle B) (p : Copy A B) :
    copySystem.Copy P C := by
  refine ⟨e.symm '' (p.val.1 ×ˢ p.val.2), ?_⟩
  obtain ⟨g, hg⟩ := p.property
  let f : bundle A ↪[folkmanLanguage] C.val := e.symm.toEmbedding.comp (encode g)
  refine ⟨hP ▸ f, ?_⟩
  cases P with
  | mk P h =>
    dsimp at hP
    subst P
    change Set.range (e.symm ∘ encode g) = _
    rw [Set.range_comp, range_encode, ← hg]

private theorem toRange_injective {A B : FolkmanNativeFiniteModel}
    {P C : folkmanFirstOrderClass} (hP : P.val = bundle A)
    (e : C.val ≃[folkmanLanguage] bundle B) :
    Function.Injective (toRange hP e) := by
  intro p q h
  apply Subtype.ext
  have he : p.val.1 ×ˢ p.val.2 = q.val.1 ×ˢ q.val.2 :=
    e.symm.injective.image_injective
      (congrArg (fun c : copySystem.Copy P C => c.val) h)
  obtain ⟨g, hg⟩ := p.property
  have hp : (p.val.1 ×ˢ p.val.2).Nonempty := by
    rw [← hg]
    exact ⟨(g.left 0, g.right 0), ⟨0, rfl⟩, ⟨0, rfl⟩⟩
  exact Prod.ext ((Set.prod_eq_prod_iff_of_nonempty hp).mp he).1
    ((Set.prod_eq_prod_iff_of_nonempty hp).mp he).2

private theorem toRange_surjective {A B : FolkmanNativeFiniteModel}
    {P C : folkmanFirstOrderClass} (hP : P.val = bundle A)
    (e : C.val ≃[folkmanLanguage] bundle B) :
    Function.Surjective (toRange hP e) := by
  cases P with
  | mk P h =>
    dsimp at hP
    subst P
    intro p
    obtain ⟨f, hf⟩ := p.property
    refine ⟨Copy.ofEmbedding (decode (e.toEmbedding.comp f)), Subtype.ext ?_⟩
    exact (range_decode e f).trans hf

private noncomputable def copyEquiv {A B : FolkmanNativeFiniteModel}
    {P C : folkmanFirstOrderClass} (hP : P.val = bundle A)
    (e : C.val ≃[folkmanLanguage] bundle B) :
    Copy A B ≃ copySystem.Copy P C :=
  Equiv.ofBijective (toRange hP e) ⟨toRange_injective hP e, toRange_surjective hP e⟩

/-- The one-atom diagonal source has infinite degree for actual first-order
copy ranges in the product-encoded class. -/
theorem copyRamseyDegree_infinite (t : ℕ) :
    ¬ copySystem.CopyRamseyDegreeLE (diagonal 1) t := by
  classical
  intro h
  let B := diagonal (2 ^ (t + 1))
  obtain ⟨C, hC⟩ := h B (2 ^ t) (by positivity)
  change folkmanFirstOrderClass at C
  obtain ⟨R, ⟨e⟩⟩ := C.property
  let W := nativeOfCode R
  let iso : C.val ≃[folkmanLanguage] bundle W := e
  let E : Copy (folkmanNativeDiagonal 1) W ≃ copySystem.Copy (diagonal 1) C :=
    copyEquiv rfl iso
  obtain ⟨colouring, hcolouring⟩ := exists_folkmanNativeCopyRangeColouring t W
  let c : copySystem.Copy (diagonal 1) C → Fin (2 ^ t) := colouring ∘ E.symm
  obtain ⟨f, hf⟩ := hC c
  change B.val ↪[folkmanLanguage] C.val at f
  let _ := copySystem.copyFintype (diagonal 1) B
  let g : Embedding (folkmanNativeDiagonal (2 ^ (t + 1))) W :=
    decode (iso.toEmbedding.comp f)
  have hall : copySystem.coloursInside c f = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro colour
    obtain ⟨p, hp, hL, hR⟩ := hcolouring g colour
    have hsub : copySystem.Subcopy (E p) (copySystem.range f) := by
      change iso.symm '' (p.val.1 ×ˢ p.val.2) ⊆ Set.range f
      calc
        _ ⊆ iso.symm '' (Set.range g.left ×ˢ Set.range g.right) :=
          Set.image_mono (Set.prod_mono hL hR)
        _ = _ := range_decode iso f
    obtain ⟨q, hq⟩ := (copySystem.subcopy_range_iff f (E p)).mp hsub
    refine Finset.mem_image.mpr ⟨q, Finset.mem_univ _, ?_⟩
    rw [hq]
    exact (congrArg colouring (E.symm_apply_apply p)).trans hp
  rw [hall, Finset.card_univ, Fintype.card_fin] at hf
  exact (Nat.not_le_of_gt t.lt_two_pow_self) hf

/-- The actual finite Folkman–BANANA class has no precompact hereditary
Ramsey expansion by adding only relations. -/
theorem not_hasPrecompactRelationalRamseyExpansion :
    ¬ FirstOrderRamseyExpansion.HasPrecompactRelationalRamseyExpansion
      folkmanFirstOrderClass :=
  FirstOrderRamseyExpansion.not_hasPrecompactRelationalRamseyExpansion
    finite_of_mem (diagonal 1) copyRamseyDegree_infinite

/-- The obstruction holds for the age of any encoded Folkman–BANANA
Fraïssé limit. -/
theorem not_hasPrecompactRelationalRamseyExpansion_age
    (M : Bundled.{0} folkmanLanguage.Structure) [Countable M]
    (hM : Language.IsFraisseLimit folkmanFirstOrderClass M) :
    ¬ FirstOrderRamseyExpansion.HasPrecompactRelationalRamseyExpansion
      (folkmanLanguage.age M) := by
  rw [hM.age]
  exact not_hasPrecompactRelationalRamseyExpansion

end FolkmanFirstOrder

end SuccessorTree.NonPrecompact
