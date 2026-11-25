import BANANA.NonPrecompact.ExpansionDegreeByIsomorphismTypes
import Mathlib.ModelTheory.Fraisse

/-!
# The expansion degree bound for finite first-order structures

First-order copy ranges form a finite copy system. Hereditary
restrictions along reduct embeddings package an actual precompact
expansion class as a Ramsey expansion of this copy system.
-/

namespace SuccessorTree.NonPrecompact

open CategoryTheory FirstOrder Function
open scoped FirstOrder

universe u v u' v' w

variable {L : Language.{u, v}} {L' : Language.{u', v'}}

private abbrev Class (L : Language.{u, v}) := Set (Bundled.{w} L.Structure)

private abbrev FirstOrderRangeCopy (A B : Bundled.{w} L.Structure) :=
  {s : Set B // ∃ e : A ↪[L] B, Set.range e = s}

private theorem embedding_factor_of_range_subset {A B C : Bundled.{w} L.Structure}
    (f : A ↪[L] C) (g : B ↪[L] C) (h : Set.range f ⊆ Set.range g) :
    ∃ e : A ↪[L] B, g.comp e = f := by
  let f' := f.codRestrict g.toHom.range fun x => h ⟨x, rfl⟩
  refine ⟨g.equivRange.symm.toEmbedding.comp f', ?_⟩
  ext x
  exact congrArg Subtype.val (g.equivRange.apply_symm_apply (f' x))

/-- Copying in an arbitrary class of finite first-order structures uses
the actual ranges of its first-order embeddings. -/
noncomputable def firstOrderFiniteCopySystem (K : Class.{u,v,w} L)
    (hK : ∀ B ∈ K, Finite B) : FiniteCopySystem where
  Obj := K
  Emb A B := A.val ↪[L] B.val
  Copy A B := FirstOrderRangeCopy A.val B.val
  idEmb A := Language.Embedding.refl L A.val
  compEmb f g := g.comp f
  comp_id_left _ := Language.Embedding.ext (fun _ => rfl)
  comp_id_right _ := Language.Embedding.ext (fun _ => rfl)
  comp_assoc _ _ _ := Language.Embedding.ext (fun _ => rfl)
  range f := ⟨Set.range f, f, rfl⟩
  mapCopy g p := ⟨g '' p.val, by
    obtain ⟨f, hf⟩ := p.property
    exact ⟨g.comp f, (Set.range_comp g f).trans (congrArg (Set.image g) hf)⟩⟩
  mapCopy_id p := by
    apply Subtype.ext
    exact Set.image_id p.val
  mapCopy_comp f g p := by
    apply Subtype.ext
    change ((g : _ → _) ∘ f) '' p.val = g '' (f '' p.val)
    exact (Set.image_image g f p.val).symm
  range_comp f g := Subtype.ext (Set.range_comp g f)
  range_surjective p := by
    obtain ⟨f, hf⟩ := p.property
    exact ⟨f, Subtype.ext hf⟩
  Subcopy p q := p.val ⊆ q.val
  subcopy_range_iff g p := by
    constructor
    · intro h
      obtain ⟨f, hf⟩ := p.property
      obtain ⟨e, he⟩ := embedding_factor_of_range_subset f g (hf.symm ▸ h)
      refine ⟨⟨Set.range e, e, rfl⟩, Subtype.ext ?_⟩
      change g '' Set.range e = p.val
      exact (Set.range_comp g e).symm.trans ((congrArg (fun m : _ ↪[L] _ => Set.range m) he).trans hf)
    · rintro ⟨q, rfl⟩
      exact Set.image_subset_range _ _
  copyFintype _ B := by
    letI := hK B.val B.property
    exact Fintype.ofFinite _
  copyDecidableEq _ _ := Classical.decEq _

/-- Genuine first-order copy ranges are unchanged by an automorphism
of the source, as required by the isomorphism-type degree bound. -/
theorem firstOrderFiniteCopySystem_range_comp_automorphism (K : Class.{u,v,w} L)
    (hK : ∀ B ∈ K, Finite B) {A B : K}
    (e : A.val ↪[L] B.val)
    (g : (firstOrderFiniteCopySystem K hK).ReductAutomorphism A) :
    (firstOrderFiniteCopySystem K hK).range ((firstOrderFiniteCopySystem K hK).compEmb g.hom e) =
      (firstOrderFiniteCopySystem K hK).range e := by
  change (⟨Set.range (e.comp g.hom), ⟨e.comp g.hom, rfl⟩⟩ : FirstOrderRangeCopy A.val B.val) =
    ⟨Set.range e, ⟨e, rfl⟩⟩
  apply Subtype.ext
  change Set.range (e.comp g.hom) = Set.range e
  let gh : A.val ↪[L] A.val := g.hom
  let gi : A.val ↪[L] A.val := g.inv
  have hright : ∀ x : A.val, gh (gi x) = x := by
    intro x
    exact congrArg (fun f : A.val ↪[L] A.val => f x) g.inv_hom
  change Set.range ((e : _ → _) ∘ gh) = Set.range e
  apply Set.Subset.antisymm (Set.range_comp_subset_range gh e)
  rintro _ ⟨x, rfl⟩
  exact ⟨gi x, congrArg e (hright x)⟩

/-- The number of expansion isomorphism types bounds the ordinary
unlabelled copy degree in a class of finite first-order structures. -/
theorem firstOrderCopyRamseyDegreeLE_card_expansionIsomorphismTypes
    {K : Class.{u,v,w} L} {hK : ∀ B ∈ K, Finite B}
    (E : RamseyExpansion (firstOrderFiniteCopySystem K hK)) (A : K) :
    (firstOrderFiniteCopySystem K hK).CopyRamseyDegreeLE A
      (Nat.card (Quotient (E.expansionIsomorphismSetoid A))) :=
  E.copyRamseyDegreeLE_card_expansionIsomorphismTypes A
    (fun e g => firstOrderFiniteCopySystem_range_comp_automorphism K hK e g)

end SuccessorTree.NonPrecompact
