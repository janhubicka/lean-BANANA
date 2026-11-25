import BANANA.NonPrecompact.FolkmanNativePairingEmbedding
import SuccessorTree.CopyRamsey

/-!
# The native Folkman–BANANA copy system

An object is a pair of finite Boolean rings with an additive pairing. The
embeddings preserve the pairing and need not preserve either ring unit.
A copy is the pair of image sets on the original ring carriers.
-/

namespace SuccessorTree.NonPrecompact

namespace FolkmanNativeFiniteModel

private theorem embedding_ext {A B : FolkmanNativeFiniteModel} {f g : Embedding A B}
    (hL : ∀ x, f.left x = g.left x) (hR : ∀ y, f.right y = g.right y) : f = g := by
  have hl : f.left = g.left := NonUnitalRingHom.ext hL
  have hr : f.right = g.right := NonUnitalRingHom.ext hR
  cases f
  cases g
  cases hl
  cases hr
  rfl

private theorem ringEmbedding_factor {A B C : Type*} [NonUnitalNonAssocRing A]
    [NonUnitalNonAssocRing B] [NonUnitalNonAssocRing C]
    (f : A →ₙ+* C) (g : B →ₙ+* C) (hg : Function.Injective g)
    (h : Set.range f ⊆ Set.range g) :
    ∃ e : A →ₙ+* B, ∀ x, g (e x) = f x := by
  classical
  have preimage (x : A) : ∃ y : B, g y = f x := h (Set.mem_range_self x)
  let pre (x : A) := Classical.choose (preimage x)
  have hpre (x : A) : g (pre x) = f x := Classical.choose_spec (preimage x)
  let e : A →ₙ+* B :=
    { toFun := pre
      map_zero' := hg (by simp only [hpre, map_zero])
      map_add' := fun x y => hg (by simp only [hpre, map_add])
      map_mul' := fun x y => hg (by simp only [hpre, map_mul]) }
  exact ⟨e, hpre⟩

/-- Native embeddings whose two ranges are contained in another embedding's
ranges factor through that embedding. -/
theorem embedding_exists_factor {A B C : FolkmanNativeFiniteModel}
    (f : Embedding A C) (g : Embedding B C)
    (hL : Set.range f.left ⊆ Set.range g.left)
    (hR : Set.range f.right ⊆ Set.range g.right) :
    ∃ e : Embedding A B, e.comp g = f := by
  obtain ⟨eL, heL⟩ := ringEmbedding_factor f.left g.left g.left_injective hL
  obtain ⟨eR, heR⟩ := ringEmbedding_factor f.right g.right g.right_injective hR
  let e : Embedding A B :=
    { left := eL
      right := eR
      left_injective := fun x y he =>
        f.left_injective ((heL x).symm.trans ((congrArg g.left he).trans (heL y)))
      right_injective := fun x y he =>
        f.right_injective ((heR x).symm.trans ((congrArg g.right he).trans (heR y)))
      preserves_pairing := fun x y => by
        rw [← g.preserves_pairing, heL, heR, f.preserves_pairing] }
  exact ⟨e, embedding_ext heL heR⟩

/-- A copy is determined by its two actual image sets. -/
abbrev Copy (A B : FolkmanNativeFiniteModel) :=
  {p : Set B.Left × Set B.Right //
    ∃ f : Embedding A B, (Set.range f.left, Set.range f.right) = p}

namespace Copy

variable {A B C : FolkmanNativeFiniteModel}

/-- Take both ring ranges of the same native embedding. -/
def ofEmbedding (f : Embedding A B) : Copy A B :=
  ⟨(Set.range f.left, Set.range f.right), f, rfl⟩

/-- Transport the two copy carriers along a native embedding. -/
def image (g : Embedding B C) (p : Copy A B) : Copy A C :=
  ⟨(g.left '' p.1.1, g.right '' p.1.2), by
    obtain ⟨f, hf⟩ := p.property
    refine ⟨f.comp g, Prod.ext ?_ ?_⟩
    · change Set.range (g.left ∘ f.left) = g.left '' p.1.1
      have hleft : Set.range f.left = p.val.1 := congrArg Prod.fst hf
      rw [Set.range_comp, hleft]
    · change Set.range (g.right ∘ f.right) = g.right '' p.1.2
      have hright : Set.range f.right = p.val.2 := congrArg Prod.snd hf
      rw [Set.range_comp, hright]⟩

end Copy
end FolkmanNativeFiniteModel

open FolkmanNativeFiniteModel

/-- Folkman–BANANA as a copy system with genuine copy ranges and native
non-unital embeddings. -/
noncomputable def folkmanNativeCopySystem : FiniteCopySystem := by
  classical
  exact {
    Obj := FolkmanNativeFiniteModel
    Emb := Embedding
    Copy := Copy
    idEmb := fun A => FolkmanNativePairingEmbedding.id A.pairing
    compEmb := fun f g => f.comp g
    comp_id_left := fun _ => embedding_ext (fun _ => rfl) (fun _ => rfl)
    comp_id_right := fun _ => embedding_ext (fun _ => rfl) (fun _ => rfl)
    comp_assoc := fun _ _ _ => embedding_ext (fun _ => rfl) (fun _ => rfl)
    range := Copy.ofEmbedding
    mapCopy := Copy.image
    mapCopy_id := fun p => Subtype.ext (Prod.ext (Set.image_id _) (Set.image_id _))
    mapCopy_comp := fun f g p => Subtype.ext (Prod.ext
      (Set.image_image g.left f.left p.1.1).symm (Set.image_image g.right f.right p.1.2).symm)
    range_comp := fun f g => Subtype.ext (Prod.ext
      (Set.range_comp g.left f.left) (Set.range_comp g.right f.right))
    range_surjective := fun p => by
      obtain ⟨f, hf⟩ := p.property
      exact ⟨f, Subtype.ext hf⟩
    Subcopy := fun p q => p.1.1 ⊆ q.1.1 ∧ p.1.2 ⊆ q.1.2
    subcopy_range_iff := fun f p => by
      constructor
      · rintro ⟨hL, hR⟩
        obtain ⟨g, hg⟩ := p.property
        have el : Set.range g.left = p.val.1 := congrArg Prod.fst hg
        have er : Set.range g.right = p.val.2 := congrArg Prod.snd hg
        have hl : Set.range g.left ⊆ Set.range f.left := by
          rw [el]
          exact hL
        have hr : Set.range g.right ⊆ Set.range f.right := by
          rw [er]
          exact hR
        obtain ⟨e, he⟩ := embedding_exists_factor g f hl hr
        refine ⟨Copy.ofEmbedding e, Subtype.ext ?_⟩
        calc
          (f.left '' Set.range e.left, f.right '' Set.range e.right) =
              (Copy.ofEmbedding (e.comp f)).val :=
            Prod.ext (Set.range_comp f.left e.left).symm (Set.range_comp f.right e.right).symm
          _ = p.val := he ▸ hg
      · rintro ⟨q, hq⟩
        rw [← hq]
        exact ⟨Set.image_subset_range _ _, Set.image_subset_range _ _⟩
    copyFintype := fun A B => Fintype.ofFinite (Copy A B)
    copyDecidableEq := fun A B => Classical.decEq (Copy A B) }

end SuccessorTree.NonPrecompact
