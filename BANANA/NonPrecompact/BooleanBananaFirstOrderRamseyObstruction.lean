import BANANA.NonPrecompact.BooleanBananaCopyTransport
import BANANA.NonPrecompact.BooleanBananaFirstOrderAge

/-!
# The copy-degree obstruction in the functional Boolean–BANANA age

Copy ranges in this age correspond to native marked-Boolean copy ranges.
This transports the persistent colouring to the actual first-order class.
-/

namespace SuccessorTree.NonPrecompact.BooleanBanana

open FirstOrder CategoryTheory
open scoped FirstOrder

local notation "M" => PrebananaFiveAryCylinderLimitCarrier
local notation "K" => markedBooleanLanguage.age M

/-- Every member of the concrete marked Boolean cylinder age is finite. -/
theorem cylinder_age_finite (B : Bundled markedBooleanLanguage.Structure) (hB : B ∈ K) :
    Finite B := by
  obtain ⟨D, ⟨e⟩⟩ := (cylinder_mem_age_iff B).mp hB
  let : Finite (firstOrderModel D) := inferInstanceAs (Finite D.carrier)
  exact Finite.of_injective e e.injective

/-- The copy system on the actual marked Boolean cylinder age. -/
noncomputable abbrev cylinderCopySystem := firstOrderFiniteCopySystem K cylinder_age_finite

/-- Regard a finite native marked Boolean model as a member of the first-order age. -/
def nativeAgeObject (A : PrebananaFiniteBooleanModel) : K :=
  ⟨firstOrderModel A, (cylinder_mem_age_iff (firstOrderModel A)).mpr
    ⟨A, ⟨Language.Equiv.refl markedBooleanLanguage _⟩⟩⟩

/-- The all-marked two-atom source in the actual first-order age. -/
def cylinderTwoMarkedAgeObject : K :=
  nativeAgeObject (booleanBananaAllMarkedPower 0)

private def toNativeEmbedding {A B : PrebananaFiniteBooleanModel}
    (f : firstOrderModel A ↪[markedBooleanLanguage] firstOrderModel B) :
    PrebananaFiniteBooleanEmbedding A B where
  hom := embeddingLatticeHom (A := A.carrier) (B := B.carrier) f
  injective := f.injective
  preserves_μ := embedding_preserves_mark (A := A.carrier) (B := B.carrier) f

private def fromNativeEmbedding {A B : PrebananaFiniteBooleanModel}
    (f : PrebananaFiniteBooleanEmbedding A B) :
    firstOrderModel A ↪[markedBooleanLanguage] firstOrderModel B :=
  latticeEmbedding (A := A.carrier) (B := B.carrier) f.hom f.injective f.preserves_μ

private def toNativeCopy {A D : PrebananaFiniteBooleanModel} {C : K}
    (e : C.val ≃[markedBooleanLanguage] firstOrderModel D)
    (p : cylinderCopySystem.Copy (nativeAgeObject A) C) : BooleanBananaCopy A D :=
  ⟨e '' p.val, by
    obtain ⟨f, hf⟩ := p.property
    refine ⟨toNativeEmbedding (e.toEmbedding.comp f), ?_⟩
    change Set.range (e ∘ f) = e '' p.val
    rw [Set.range_comp, hf]⟩

private def fromNativeCopy {A D : PrebananaFiniteBooleanModel} {C : K}
    (e : C.val ≃[markedBooleanLanguage] firstOrderModel D)
    (p : BooleanBananaCopy A D) : cylinderCopySystem.Copy (nativeAgeObject A) C :=
  ⟨e.symm '' p.val, by
    obtain ⟨f, hf⟩ := p.property
    refine ⟨e.symm.toEmbedding.comp (fromNativeEmbedding f), ?_⟩
    let g : D.carrier → C.val := e.symm
    change Set.range (g ∘ f.hom) = g '' p.val
    rw [Set.range_comp, hf]⟩

private theorem toNativeCopy_fromNativeCopy {A D : PrebananaFiniteBooleanModel} {C : K}
    (e : C.val ≃[markedBooleanLanguage] firstOrderModel D)
    (p : BooleanBananaCopy A D) : toNativeCopy e (fromNativeCopy e p) = p := by
  apply Subtype.ext
  let f : C.val → D.carrier := e
  let g : D.carrier → C.val := e.symm
  change f '' (g '' p.val) = p.val
  rw [Set.image_image]
  have he : (fun x => f (g x)) = id := funext e.apply_symm_apply
  rw [he, Set.image_id]

/-- Every first-order ambient structure admits a colouring of the
all-marked two-atom source exhibiting every colour in each target copy. -/
theorem exists_cylinderPersistentColouring (k : ℕ) (C : K) :
    ∃ colouring : cylinderCopySystem.Copy cylinderTwoMarkedAgeObject C → Fin (2 ^ k),
      ∀ (f : cylinderCopySystem.Emb (nativeAgeObject (booleanBananaAllMarkedPower k)) C)
        (colour : Fin (2 ^ k)),
        ∃ q : cylinderCopySystem.Copy cylinderTwoMarkedAgeObject C,
          colouring q = colour ∧ cylinderCopySystem.Subcopy q (cylinderCopySystem.range f) := by
  obtain ⟨D, ⟨e⟩⟩ := (cylinder_mem_age_iff C.val).mp C.property
  obtain ⟨c, hc⟩ := exists_booleanBananaPersistentColouring k D
  refine ⟨fun p => c (toNativeCopy e p), fun f colour => ?_⟩
  let g : PrebananaFiniteBooleanEmbedding (booleanBananaAllMarkedPower k) D :=
    toNativeEmbedding (e.toEmbedding.comp f)
  obtain ⟨p, hp, hsub⟩ := hc g colour
  refine ⟨fromNativeCopy e p, ?_, ?_⟩
  · exact (congrArg c (toNativeCopy_fromNativeCopy e p)).trans hp
  · let f' : (nativeAgeObject (booleanBananaAllMarkedPower k)).val ↪[markedBooleanLanguage] C.val := f
    change e.symm '' p.val ⊆ Set.range f'
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy⟩ := hsub hx
    refine ⟨y, ?_⟩
    change e (f' y) = x at hy
    exact (e.symm_apply_apply (f' y)).symm.trans (congrArg e.symm hy)

/-- The all-marked two-atom source has infinite copy Ramsey degree in
the ordinary first-order age, with copies taken as actual image ranges. -/
theorem cylinderTwoMarkedCopyRamseyDegree_infinite (t : ℕ) :
    ¬ cylinderCopySystem.CopyRamseyDegreeLE cylinderTwoMarkedAgeObject t := by
  classical
  intro h
  let B := nativeAgeObject (booleanBananaAllMarkedPower t)
  obtain ⟨C, hC⟩ := h B (2 ^ t) (by positivity)
  obtain ⟨colouring, hcolouring⟩ := exists_cylinderPersistentColouring t C
  obtain ⟨f, hf⟩ := hC colouring
  let := cylinderCopySystem.copyFintype cylinderTwoMarkedAgeObject B
  have hall : cylinderCopySystem.coloursInside colouring f = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro colour
    obtain ⟨p, hp, hsub⟩ := hcolouring f colour
    obtain ⟨q, hq⟩ := (cylinderCopySystem.subcopy_range_iff f p).mp hsub
    exact Finset.mem_image.mpr ⟨q, Finset.mem_univ _, (congrArg colouring hq).trans hp⟩
  rw [hall, Finset.card_univ, Fintype.card_fin] at hf
  exact t.lt_two_pow_self.not_ge hf

/-- The hereditary, precompact embedding-Ramsey obstruction for relational
expansions of the actual functional Boolean–BANANA age. -/
theorem cylinder_noPrecompactRelationalRamseyExpansion :
    ¬ FirstOrderRamseyExpansion.HasPrecompactRelationalRamseyExpansion K :=
  FirstOrderRamseyExpansion.not_hasPrecompactRelationalRamseyExpansion
    cylinder_age_finite cylinderTwoMarkedAgeObject cylinderTwoMarkedCopyRamseyDegree_infinite

end SuccessorTree.NonPrecompact.BooleanBanana
