import BANANA.NonPrecompact.BananaFunctionalLimit
import BANANA.NonPrecompact.BananaNativeCopySystem
import BANANA.NonPrecompact.FirstOrderRamseyExpansion

/-!
# Copy Ramsey degree in the functional BANANA age

Matrix presentations cover the genuine first-order age up to isomorphism.
An unlabelled copy in the functional language is the union of the tagged
images of its two native linear maps. This identification transfers copy
colourings and the infinite-degree obstruction to the first-order age.
-/

namespace SuccessorTree.NonPrecompact.BananaFunctional

open FirstOrder CategoryTheory
open scoped FirstOrder

/-- The genuine first-order age of the explicit functional BANANA limit. -/
abbrev functionalAge :=
  bananaFunctionalLanguage.age BananaTaggedCarrier

/-- Every member of the functional age has finite carrier. -/
theorem finite_of_mem_functionalAge (B : Bundled bananaFunctionalLanguage.Structure)
    (hB : B ∈ functionalAge) : Finite B := by
  let e := hB.2.some
  let _ := finite_of_fg e.toHom.range (hB.1.range e.toHom)
  exact Finite.of_injective e.equivRange e.equivRange.injective

/-- The copy system of the functional age uses actual embedding images. -/
noncomputable abbrev functionalCopySystem :=
  firstOrderFiniteCopySystem functionalAge finite_of_mem_functionalAge

private abbrev MatrixCarrier (A : BananaFiniteCopyObject) :=
  (Fin A.leftDim → F2) ⊕ (Fin A.rightDim → F2)

private abbrev matrixModel (A : BananaFiniteCopyObject) :
    Bundled bananaFunctionalLanguage.Structure :=
  ⟨MatrixCarrier A, structureOn A.matrix.eval⟩

private theorem matrixModel_mem (A : BananaFiniteCopyObject) : matrixModel A ∈ functionalAge := by
  let a := A.matrix.embeds_in_explicit_limit.some
  let := structureOn A.matrix.eval
  exact ⟨Language.Structure.FG.of_finite, ⟨embedding A.matrix.eval bananaLimitPairing
    a.left a.right a.left_injective a.right_injective a.pairing_apply⟩⟩

/-- A finite matrix presentation as a member of the functional age. -/
def matrixAgeObject (A : BananaFiniteCopyObject) : functionalAge :=
  ⟨matrixModel A, matrixModel_mem A⟩

private abbrev AgeEmb (A B : functionalAge) :=
  A.val ↪[bananaFunctionalLanguage] B.val

private def matrixEmbeddingEquiv (A B : BananaFiniteCopyObject) :
    BananaMatrixEmbedding A.matrix B.matrix ≃ AgeEmb (matrixAgeObject A) (matrixAgeObject B) where
  toFun f := embedding A.matrix.eval B.matrix.eval f.left f.right
    f.left_injective f.right_injective f.pairing_apply
  invFun f := ⟨leftLinear A.matrix.eval B.matrix.eval f, rightLinear A.matrix.eval B.matrix.eval f,
    leftLinear_injective A.matrix.eval B.matrix.eval f, rightLinear_injective A.matrix.eval B.matrix.eval f,
    map_pairing A.matrix.eval B.matrix.eval f⟩
  left_inv f := by
    cases f
    rfl
  right_inv f := by
    let := structureOn A.matrix.eval
    let := structureOn B.matrix.eval
    apply Language.Embedding.ext
    intro x
    cases x with
    | inl x => exact (map_inl_linear A.matrix.eval B.matrix.eval f x).symm
    | inr y => exact (map_inr_linear A.matrix.eval B.matrix.eval f y).symm

private theorem matrixEmbeddingEquiv_comp {A B C : BananaFiniteCopyObject}
    (f : BananaMatrixEmbedding A.matrix B.matrix) (g : BananaMatrixEmbedding B.matrix C.matrix) :
    matrixEmbeddingEquiv A C (g.comp f) =
      functionalCopySystem.compEmb (matrixEmbeddingEquiv A B f) (matrixEmbeddingEquiv B C g) := by
  let := structureOn A.matrix.eval
  let := structureOn C.matrix.eval
  apply Language.Embedding.ext
  intro x
  cases x <;> rfl

private theorem exists_matrixModelEquiv (B : functionalAge) :
    ∃ A : BananaFiniteCopyObject,
      Nonempty ((matrixAgeObject A).val ≃[bananaFunctionalLanguage] B.val) := by
  obtain ⟨S, hS, ⟨e⟩⟩ := age_member_native B.val B.property
  let U := leftSubspace bananaLimitPairing S
  let V := rightSubspace bananaLimitPairing S
  let : Finite S := hS
  let : Finite U := finite_leftSubspace bananaLimitPairing S
  let : Finite V := finite_rightSubspace bananaLimitPairing S
  obtain ⟨l, r, A, f, hL, hR⟩ := exists_finite_banana_substructure_of_limit U V
  let EL : (Fin l → F2) ≃ₗ[F2] U :=
    (LinearEquiv.ofInjective f.left f.left_injective).trans (LinearEquiv.ofEq _ _ hL)
  let ER : (Fin r → F2) ≃ₗ[F2] V :=
    (LinearEquiv.ofInjective f.right f.right_injective).trans (LinearEquiv.ofEq _ _ hR)
  let β := restrictedPairing bananaLimitPairing S
  let := structureOn A.eval
  let := structureOn β
  let E : ((Fin l → F2) ⊕ (Fin r → F2)) ≃[bananaFunctionalLanguage] (U ⊕ V) :=
    let g := embedding A.eval β EL.toLinearMap ER.toLinearMap
      EL.injective ER.injective f.pairing_apply
    { toEquiv := EL.toEquiv.sumCongr ER.toEquiv
      map_fun' := g.map_fun
      map_rel' := g.map_rel }
  exact ⟨⟨l, r, A⟩, ⟨e.symm.comp E⟩⟩

private def taggedRange {A B : BananaFiniteCopyObject}
    (p : BananaCopyRanges A.matrix B.matrix) : Set (MatrixCarrier B) :=
  Sum.inl '' (p.val.1 : Set (Fin B.leftDim → F2)) ∪
    Sum.inr '' (p.val.2 : Set (Fin B.rightDim → F2))

private theorem inl_mem_taggedRange {A B : BananaFiniteCopyObject}
    (p : BananaCopyRanges A.matrix B.matrix) (x : Fin B.leftDim → F2) :
    Sum.inl x ∈ taggedRange p ↔ x ∈ p.val.1 := by
  simp [taggedRange]

private theorem inr_mem_taggedRange {A B : BananaFiniteCopyObject}
    (p : BananaCopyRanges A.matrix B.matrix) (y : Fin B.rightDim → F2) :
    Sum.inr y ∈ taggedRange p ↔ y ∈ p.val.2 := by
  simp [taggedRange]

private theorem taggedRange_injective {A B : BananaFiniteCopyObject} :
    Function.Injective (@taggedRange A B) := by
  intro p q h
  apply Subtype.ext
  apply Prod.ext
  · ext x
    rw [← inl_mem_taggedRange p, h, inl_mem_taggedRange]
  · ext y
    rw [← inr_mem_taggedRange p, h, inr_mem_taggedRange]

private theorem taggedRange_of_embedding {A B : BananaFiniteCopyObject}
    (f : BananaMatrixEmbedding A.matrix B.matrix) :
    taggedRange f.copyRanges = Set.range (matrixEmbeddingEquiv A B f) := by
  classical
  ext z
  cases z with
  | inl x =>
    rw [inl_mem_taggedRange]
    change x ∈ Finset.univ.image f.left ↔
      (∃ a : MatrixCarrier A, Sum.map f.left f.right a = Sum.inl x)
    constructor
    · intro hx
      obtain ⟨y, -, hy⟩ := Finset.mem_image.mp hx
      exact ⟨Sum.inl y, congrArg Sum.inl hy⟩
    · rintro ⟨a, ha⟩
      cases a with
      | inl a => exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, Sum.inl.inj ha⟩
      | inr a => cases ha
  | inr y =>
    rw [inr_mem_taggedRange]
    change y ∈ Finset.univ.image f.right ↔
      (∃ a : MatrixCarrier A, Sum.map f.left f.right a = Sum.inr y)
    constructor
    · intro hy
      obtain ⟨x, -, hx⟩ := Finset.mem_image.mp hy
      exact ⟨Sum.inr x, congrArg Sum.inr hx⟩
    · rintro ⟨a, ha⟩
      cases a with
      | inl a => cases ha
      | inr a => exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, Sum.inr.inj ha⟩

private noncomputable def copyRangeMap {A B : BananaFiniteCopyObject}
    (p : BananaCopyRanges A.matrix B.matrix) :
    functionalCopySystem.Copy (matrixAgeObject A) (matrixAgeObject B) := by
  refine ⟨taggedRange p, ?_⟩
  obtain ⟨f, hf, hg⟩ := p.property
  have he : p = f.copyRanges := Subtype.ext (Prod.ext hf hg)
  exact ⟨matrixEmbeddingEquiv A B f, (taggedRange_of_embedding f).symm.trans (congrArg taggedRange he.symm)⟩

private theorem copyRangeMap_range {A B : BananaFiniteCopyObject}
    (f : BananaMatrixEmbedding A.matrix B.matrix) :
    copyRangeMap f.copyRanges = functionalCopySystem.range (matrixEmbeddingEquiv A B f) :=
  Subtype.ext (taggedRange_of_embedding f)

private noncomputable def copyRangeEquiv (A B : BananaFiniteCopyObject) :
    BananaCopyRanges A.matrix B.matrix ≃
      functionalCopySystem.Copy (matrixAgeObject A) (matrixAgeObject B) :=
  Equiv.ofBijective copyRangeMap ⟨fun _ _ h =>
    taggedRange_injective (congrArg Subtype.val h), fun q => by
    obtain ⟨g, rfl⟩ := functionalCopySystem.range_surjective q
    obtain ⟨f, rfl⟩ := (matrixEmbeddingEquiv A B).surjective g
    exact ⟨f.copyRanges, copyRangeMap_range f⟩⟩

private theorem copyRangeEquiv_natural {A B C : BananaFiniteCopyObject}
    (g : BananaMatrixEmbedding B.matrix C.matrix) (p : BananaCopyRanges A.matrix B.matrix) :
    copyRangeEquiv A C (p.map g) =
      functionalCopySystem.mapCopy (matrixEmbeddingEquiv B C g) (copyRangeEquiv A B p) := by
  obtain ⟨f, hf, hg⟩ := p.property
  have he : p = f.copyRanges := Subtype.ext (Prod.ext hf hg)
  subst p
  change copyRangeMap (f.copyRanges.map g) =
    functionalCopySystem.mapCopy (matrixEmbeddingEquiv B C g) (copyRangeMap f.copyRanges)
  rw [BananaMatrixEmbedding.copyRanges_comp, copyRangeMap_range, copyRangeMap_range,
    matrixEmbeddingEquiv_comp]
  exact functionalCopySystem.range_comp (matrixEmbeddingEquiv A B f) (matrixEmbeddingEquiv B C g)

/-- A degree bound in the functional age gives the same bound on matrix
presentations. The colouring is pulled back along a matrix representative of
the entire Ramsey witness, so its copy ranges remain genuinely unlabelled. -/
theorem matrixCopyRamseyDegreeLE_of_ageCopyRamseyDegreeLE (A : BananaFiniteCopyObject) {t : ℕ}
    (h : functionalCopySystem.CopyRamseyDegreeLE (matrixAgeObject A) t) :
    bananaCopySystem.CopyRamseyDegreeLE A t := by
  classical
  intro B r hr
  obtain ⟨C, hC⟩ := h (matrixAgeObject B) r hr
  obtain ⟨D, ⟨e⟩⟩ := exists_matrixModelEquiv C
  let j := e.symm.toEmbedding
  refine ⟨D, fun c => ?_⟩
  let c' : functionalCopySystem.Copy (matrixAgeObject A) C → Fin r :=
    fun p => c ((copyRangeEquiv A D).symm (functionalCopySystem.mapCopy j p))
  obtain ⟨f, hf⟩ := hC c'
  let g := (matrixEmbeddingEquiv B D).symm (functionalCopySystem.compEmb f j)
  refine ⟨g, (Finset.card_le_card ?_).trans hf⟩
  let _ := functionalCopySystem.copyFintype (matrixAgeObject A) (matrixAgeObject B)
  intro y hy
  obtain ⟨p, -, hp⟩ := Finset.mem_image.mp hy
  refine Finset.mem_image.mpr ⟨copyRangeEquiv A B p, Finset.mem_univ _, ?_⟩
  rw [← hp]
  change c ((copyRangeEquiv A D).symm (functionalCopySystem.mapCopy j
      (functionalCopySystem.mapCopy f (copyRangeEquiv A B p)))) = c (p.map g)
  have hg : functionalCopySystem.compEmb f j = matrixEmbeddingEquiv B D g :=
    ((matrixEmbeddingEquiv B D).apply_symm_apply (functionalCopySystem.compEmb f j)).symm
  have hMap :
      functionalCopySystem.mapCopy j (functionalCopySystem.mapCopy f (copyRangeEquiv A B p)) =
        copyRangeEquiv A D (p.map g) :=
    (functionalCopySystem.mapCopy_comp f j (copyRangeEquiv A B p)).symm.trans <|
      (congrArg (fun e => functionalCopySystem.mapCopy e (copyRangeEquiv A B p)) hg).trans
        (copyRangeEquiv_natural g p).symm
  exact (congrArg (fun q => c ((copyRangeEquiv A D).symm q)) hMap).trans
    (congrArg c ((copyRangeEquiv A D).symm_apply_apply (p.map g)))

/-- A four-element BANANA pairing has infinite copy Ramsey degree in the
actual functional first-order age. -/
theorem linePair_infinite_copyRamseyDegree (t : ℕ) :
    ¬ functionalCopySystem.CopyRamseyDegreeLE (matrixAgeObject ⟨1, 1, linePairSource 0⟩) t := by
  intro h
  let A : BananaFiniteCopyObject := ⟨1, 1, linePairSource 0⟩
  have h' := matrixCopyRamseyDegreeLE_of_ageCopyRamseyDegreeLE A h
  exact A.matrix.copyRamseyDegree_infinite_of_positive (by decide) (by decide) t
    ((bananaCopySystem_copyRamseyDegreeLE_iff A t).mp h')

/-- The actual age of the functional BANANA limit has no hereditary
precompact Ramsey expansion by added relations. -/
theorem functionalAge_noPrecompactRelationalRamseyExpansion :
    ¬ FirstOrderRamseyExpansion.HasPrecompactRelationalRamseyExpansion functionalAge :=
  FirstOrderRamseyExpansion.not_hasPrecompactRelationalRamseyExpansion
    finite_of_mem_functionalAge (matrixAgeObject ⟨1, 1, linePairSource 0⟩)
      linePair_infinite_copyRamseyDegree

end SuccessorTree.NonPrecompact.BananaFunctional
