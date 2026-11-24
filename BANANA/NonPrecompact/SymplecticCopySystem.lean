import BANANA.NonPrecompact.SymplecticCountableModel
import SuccessorTree.CopyRamsey

/-!
# The finite age of the countable symplectic space as a copy system

Objects are finite-dimensional alternating spaces over `F₂`. An embedded
copy is the image subspace, with the inherited form. The already verified
age and homogeneity of the countable model supply amalgamation.
-/

namespace SuccessorTree.NonPrecompact

open LinearMap Module

/-- A finite-dimensional alternating space over the binary field. -/
structure FiniteAlternatingSpace where
  carrier : Type
  [addCommGroup : AddCommGroup carrier]
  [module : Module F2 carrier]
  [finiteDimensional : FiniteDimensional F2 carrier]
  form : LinearMap.BilinForm F2 carrier
  alternating : form.IsAlt

attribute [instance] FiniteAlternatingSpace.addCommGroup FiniteAlternatingSpace.module
  FiniteAlternatingSpace.finiteDimensional

namespace FiniteAlternatingSpace

/-- An injective linear embedding preserving the form. -/
structure Embedding (A B : FiniteAlternatingSpace) where
  linear : A.carrier →ₗ[F2] B.carrier
  injective : Function.Injective linear
  preserves_form : ∀ x y, B.form (linear x) (linear y) = A.form x y

namespace Embedding

variable {A B C : FiniteAlternatingSpace}

@[ext]
theorem ext {f g : Embedding A B} (h : ∀ x, f.linear x = g.linear x) : f = g := by
  have hlin : f.linear = g.linear := LinearMap.ext h
  cases f
  cases g
  cases hlin
  rfl

def id (A : FiniteAlternatingSpace) : Embedding A A where
  linear := LinearMap.id
  injective := Function.injective_id
  preserves_form _ _ := rfl

def comp (g : Embedding B C) (f : Embedding A B) : Embedding A C where
  linear := g.linear.comp f.linear
  injective := g.injective.comp f.injective
  preserves_form x y := (g.preserves_form (f.linear x) (f.linear y)).trans (f.preserves_form x y)

/-- An embedding with image contained in that of another embedding
factors through the second embedding. -/
theorem exists_factor (f : Embedding A C) (g : Embedding B C)
    (h : LinearMap.range f.linear ≤ LinearMap.range g.linear) :
    ∃ i : Embedding A B, g.comp i = f := by
  let e := LinearEquiv.ofInjective g.linear g.injective
  let f' := f.linear.codRestrict (LinearMap.range g.linear) (fun x => h (mem_range_self _ x))
  let L := e.symm.toLinearMap.comp f'
  have hL (x : A.carrier) : g.linear (L x) = f.linear x :=
    LinearEquiv.ofInjective_symm_apply g.linear (h := g.injective) (f' x)
  refine ⟨⟨L, ?_, ?_⟩, Embedding.ext hL⟩
  · intro x y hxy
    apply f.injective
    rw [← hL x, ← hL y, hxy]
  · intro x y
    rw [← g.preserves_form, hL, hL, f.preserves_form]

end Embedding

/-- An unlabelled copy in a finite alternating space is an actual subspace. -/
abbrev Copy (A B : FiniteAlternatingSpace) :=
  {S : Submodule F2 B.carrier // ∃ f : Embedding A B, LinearMap.range f.linear = S}

namespace Copy

variable {A B C : FiniteAlternatingSpace}

def ofEmbedding (f : Embedding A B) : Copy A B := ⟨LinearMap.range f.linear, f, rfl⟩

def map (g : Embedding B C) (p : Copy A B) : Copy A C :=
  ⟨p.val.map g.linear, by
    obtain ⟨f, hf⟩ := p.property
    exact ⟨g.comp f, (LinearMap.range_comp _ _).trans (congrArg (Submodule.map g.linear) hf)⟩⟩

end Copy

/-- The copy system of all finite alternating spaces over the binary field. -/
noncomputable def copySystem : FiniteCopySystem := by
  classical
  exact {
    Obj := FiniteAlternatingSpace
    Emb := Embedding
    Copy := Copy
    idEmb := Embedding.id
    compEmb := fun f g => g.comp f
    comp_id_left := fun f => Embedding.ext (fun _ => rfl)
    comp_id_right := fun f => Embedding.ext (fun _ => rfl)
    comp_assoc := fun f g h => Embedding.ext (fun _ => rfl)
    range := Copy.ofEmbedding
    mapCopy := Copy.map
    mapCopy_id := fun p => Subtype.ext (Submodule.map_id _)
    mapCopy_comp := fun f g p => Subtype.ext (Submodule.map_comp _ _ _)
    range_comp := fun f g => Subtype.ext (LinearMap.range_comp _ _)
    range_surjective := fun p => by
      obtain ⟨f, hf⟩ := p.property
      exact ⟨f, Subtype.ext hf⟩
    Subcopy := fun p q => p.val ≤ q.val
    subcopy_range_iff := fun f p => by
      constructor
      · intro h
        obtain ⟨g, hg⟩ := p.property
        obtain ⟨i, hi⟩ := g.exists_factor f (hg.symm ▸ h)
        refine ⟨Copy.ofEmbedding i, Subtype.ext ?_⟩
        change (LinearMap.range i.linear).map f.linear = p.val
        rw [← LinearMap.range_comp]
        exact (congrArg (fun j : Embedding _ _ => LinearMap.range j.linear) hi).trans hg
      · rintro ⟨q, hq⟩
        rw [← hq]
        change q.val.map f.linear ≤ LinearMap.range f.linear
        rw [← Submodule.map_top]
        exact Submodule.map_mono le_top
    copyFintype := fun A B => by
      letI : Finite B.carrier := Module.finite_of_finite F2
      letI : Finite (Copy A B) := Finite.of_injective
        (fun p : Copy A B => (p.val : Set B.carrier))
        (fun _ _ h => Subtype.ext (SetLike.coe_injective h))
      exact Fintype.ofFinite _
    copyDecidableEq := fun _ _ => Classical.decEq _
  }

/-- Amalgamation follows from the exact finite age and homogeneity of the
countable symplectic space. The join of two embedded images is finite. -/
theorem exists_amalgam {P B A : FiniteAlternatingSpace}
    (p : Embedding P B) (a : Embedding P A) :
    ∃ (D : FiniteAlternatingSpace) (i : Embedding B D) (j : Embedding A D),
      i.comp p = j.comp a := by
  obtain ⟨b, hb, hbform⟩ := (countableSymplectic_finite_age B.form).mp B.alternating
  obtain ⟨c, hc, hcform⟩ := (countableSymplectic_finite_age A.form).mp A.alternating
  let bP := b.comp p.linear
  let cP := c.comp a.linear
  let e := LinearEquiv.ofInjective bP (hb.comp p.injective)
  let f := cP.comp e.symm.toLinearMap
  have hfb (x : P.carrier) : f (e x) = cP x := by simp [f]
  obtain ⟨g, hgform, hg⟩ := exists_countableSymplectic_automorphism
    (LinearMap.range bP) f ((hc.comp a.injective).comp e.symm.injective) (by
      intro u v
      obtain ⟨x, rfl⟩ := e.surjective u
      obtain ⟨y, rfl⟩ := e.surjective v
      rw [hfb, hfb]
      change countableSymplecticForm (c (a.linear x)) (c (a.linear y)) =
        countableSymplecticForm (b (p.linear x)) (b (p.linear y))
      rw [hcform, hbform, a.preserves_form, p.preserves_form])
  let bg := g.toLinearMap.comp b
  let S := LinearMap.range bg ⊔ LinearMap.range c
  let D : FiniteAlternatingSpace :=
    { carrier := S
      addCommGroup := inferInstance
      module := inferInstance
      finiteDimensional := inferInstance
      form := countableSymplecticForm.restrict S
      alternating := fun x => countableSymplecticForm_isAlt x.val }
  have hbg : LinearMap.range bg ≤ S := le_sup_left
  have hcS : LinearMap.range c ≤ S := le_sup_right
  let i : Embedding B D :=
    ⟨bg.codRestrict S (fun x => hbg (mem_range_self _ x)),
      fun _ _ h => (g.injective.comp hb) (congrArg Subtype.val h),
      fun x y => (hgform (b x) (b y)).trans (hbform x y)⟩
  let j : Embedding A D :=
    ⟨c.codRestrict S (fun x => hcS (mem_range_self _ x)),
      fun _ _ h => hc (congrArg Subtype.val h), hcform⟩
  refine ⟨D, i, j, Embedding.ext (fun x => Subtype.ext ?_)⟩
  exact (hg (e x)).trans (hfb x)

/-- The amalgamation square needed for propagation of copy Ramsey degrees. -/
theorem amalgamation : AmalgamationSystem copySystem where
  amalgamate := exists_amalgam

end FiniteAlternatingSpace

end SuccessorTree.NonPrecompact
