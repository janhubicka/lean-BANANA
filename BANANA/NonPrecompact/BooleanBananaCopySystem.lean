import BANANA.NonPrecompact.PrebananaFiniteBooleanModelEmbeddingCalculus
import SuccessorTree.CopyRamsey

/-!
# Copies in finite Boolean–BANANA structures

Copies are ranges of marked Boolean embeddings. The copy operations and
containment are the set-theoretic image and inclusion on the original
Boolean carriers.
-/

namespace SuccessorTree.NonPrecompact

private theorem booleanEmbedding_ext
    {A B : PrebananaFiniteBooleanModel}
    {f g : PrebananaFiniteBooleanEmbedding A B}
    (h : ∀ x, f.hom x = g.hom x) : f = g := by
  have heq : f.hom = g.hom := BoundedLatticeHom.ext h
  cases f
  cases g
  cases heq
  rfl

/-- If one marked Boolean embedding has range in another, it factors
through that embedding by a marked Boolean embedding. -/
theorem booleanBananaEmbedding_exists_factor
    {A B C : PrebananaFiniteBooleanModel}
    (f : PrebananaFiniteBooleanEmbedding A C)
    (g : PrebananaFiniteBooleanEmbedding B C)
    (h : Set.range f.hom ⊆ Set.range g.hom) :
    ∃ e : PrebananaFiniteBooleanEmbedding A B, g.comp e = f := by
  classical
  have hpre (x : A.carrier) : ∃ y : B.carrier, g.hom y = f.hom x :=
    h (Set.mem_range_self x)
  let e : A.carrier → B.carrier := fun x => Classical.choose (hpre x)
  have he (x : A.carrier) : g.hom (e x) = f.hom x :=
    Classical.choose_spec (hpre x)
  let e' : PrebananaFiniteBooleanEmbedding A B := {
    hom := {
      toFun := e
      map_bot' := g.injective (by simp only [he, map_bot])
      map_top' := g.injective (by simp only [he, map_top])
      map_sup' := fun x y =>
        g.injective (by simp only [he, map_sup])
      map_inf' := fun x y =>
        g.injective (by simp only [he, map_inf])
    }
    injective := fun x y hxy => f.injective (by
      change e x = e y at hxy
      rw [← he x, ← he y, hxy])
    preserves_μ := fun x => by
      change B.μ (e x) = A.μ x
      rw [← g.preserves_μ, he, f.preserves_μ] }
  exact ⟨e', booleanEmbedding_ext he⟩

/-- The copy-range type on the actual carrier of a finite Boolean–BANANA structure. -/
abbrev BooleanBananaCopy (A B : PrebananaFiniteBooleanModel) :=
  {s : Set B.carrier // ∃ f : PrebananaFiniteBooleanEmbedding A B, Set.range f.hom = s}

namespace BooleanBananaCopy

variable {A B C : PrebananaFiniteBooleanModel}

/-- Construct the copy carried by the range of an embedding. -/
def ofEmbedding (f : PrebananaFiniteBooleanEmbedding A B) : BooleanBananaCopy A B :=
  ⟨Set.range f.hom, f, rfl⟩

/-- Transport a copy by taking its image under a marked embedding. -/
def image (f : PrebananaFiniteBooleanEmbedding B C) (p : BooleanBananaCopy A B) :
    BooleanBananaCopy A C :=
  ⟨f.hom '' p.1, by
    obtain ⟨e, he⟩ := p.2
    refine ⟨f.comp e, ?_⟩
    change Set.range (f.hom ∘ e.hom) = f.hom '' p.1
    rw [Set.range_comp, he]⟩

end BooleanBananaCopy

/-- The copy system of finite Boolean–BANANA structures in the original
Boolean language. It uses ranges, so distinct embeddings of the same
copy give equal elements of the copy type. -/
noncomputable def booleanBananaCopySystem : FiniteCopySystem := by
  classical
  exact {
    Obj := PrebananaFiniteBooleanModel
    Emb := PrebananaFiniteBooleanEmbedding
    Copy := BooleanBananaCopy
    idEmb := PrebananaFiniteBooleanEmbedding.id
    compEmb := fun f g => g.comp f
    comp_id_left := fun f => booleanEmbedding_ext (fun _ => rfl)
    comp_id_right := fun f => booleanEmbedding_ext (fun _ => rfl)
    comp_assoc := fun f g h => booleanEmbedding_ext (fun _ => rfl)
    range := BooleanBananaCopy.ofEmbedding
    mapCopy := BooleanBananaCopy.image
    mapCopy_id := fun p => Subtype.ext (Set.image_id _)
    mapCopy_comp := fun f g p => Subtype.ext (Set.image_image g.hom f.hom p.1).symm
    range_comp := fun f g => Subtype.ext (Set.range_comp g.hom f.hom)
    range_surjective := fun p => by
      obtain ⟨f, hf⟩ := p.2
      exact ⟨f, Subtype.ext hf⟩
    Subcopy := fun p q => p.1 ⊆ q.1
    subcopy_range_iff := fun f p => by
      constructor
      · intro h
        obtain ⟨g, hg⟩ := p.2
        have hgf : Set.range g.hom ⊆ Set.range f.hom := by rw [hg]; exact h
        obtain ⟨e, he⟩ := booleanBananaEmbedding_exists_factor g f hgf
        refine ⟨BooleanBananaCopy.ofEmbedding e, Subtype.ext ?_⟩
        change f.hom '' Set.range e.hom = p.1
        rw [← Set.range_comp]
        exact (congrArg (fun k : PrebananaFiniteBooleanEmbedding _ _ =>
          Set.range k.hom) he).trans hg
      · rintro ⟨q, hq⟩
        rw [← hq]
        exact Set.image_subset_range _ _
    copyFintype := fun A B => Fintype.ofFinite (BooleanBananaCopy A B)
    copyDecidableEq := fun A B => Classical.decEq (BooleanBananaCopy A B)
  }

end SuccessorTree.NonPrecompact
