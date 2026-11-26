import BANANA.NonPrecompact.ExpansionDegreeByIsomorphismTypes

/-!
# Embeddings with a prescribed image

In a copy system with cancellation and factorisation, the embeddings onto
a fixed copy form a torsor under the automorphisms of the source.
-/

namespace SuccessorTree.FiniteCopySystem

open Function

variable {S : FiniteCopySystem} {A : S.Obj}

/-- The two embedding maps determine the reduct automorphism. -/
theorem ReductAutomorphism.ext {f g : S.ReductAutomorphism A}
    (hom : f.hom = g.hom) (inv : f.inv = g.inv) : f = g := by
  cases f
  cases g
  cases hom
  cases inv
  rfl

/-- A self-embedding of a finite structure is an automorphism. This
constructs its inverse by factoring the identity through its full range. -/
noncomputable def selfEmbeddingEquivReductAutomorphism
    (cancel : ∀ {B} (g : S.Emb A B),
      Injective (fun f : S.Emb A A => S.compEmb f g))
    (factor : ∀ {B} (f g : S.Emb A B), S.range f = S.range g →
      ∃ e : S.Emb A A, S.compEmb e g = f)
    (full : ∀ f : S.Emb A A, S.range f = S.range (S.idEmb A)) :
    S.Emb A A ≃ S.ReductAutomorphism A where
  toFun f :=
    let h := factor (S.idEmb A) f (full f).symm
    ⟨f, h.choose, cancel f (by
      change S.compEmb (S.compEmb f h.choose) f = S.compEmb (S.idEmb A) f
      rw [S.comp_assoc, h.choose_spec, S.comp_id_right, S.comp_id_left]), h.choose_spec⟩
  invFun f := f.hom
  left_inv _ := rfl
  right_inv f := by
    have h := factor (S.idEmb A) f.hom (full f.hom).symm
    exact ReductAutomorphism.ext rfl (cancel f.hom (h.choose_spec.trans f.inv_hom.symm))

/-- After choosing one embedding onto a copy, all others are obtained
uniquely by precomposing it with a self-embedding. -/
noncomputable def embeddingFibreEquivSelf
    (cancel : ∀ {B} (g : S.Emb A B),
      Injective (fun f : S.Emb A A => S.compEmb f g))
    (factor : ∀ {B} (f g : S.Emb A B), S.range f = S.range g →
      ∃ e : S.Emb A A, S.compEmb e g = f)
    (full : ∀ f : S.Emb A A, S.range f = S.range (S.idEmb A))
    {B : S.Obj} (p : S.Copy A B) :
    {f : S.Emb A B // S.range f = p} ≃ S.Emb A A := by
  let witness := S.range_surjective p
  let g := witness.choose
  have hg : S.range g = p := witness.choose_spec
  exact (Equiv.ofBijective
    (fun e : S.Emb A A =>
      (⟨S.compEmb e g, by rw [S.range_comp, full e, ← S.range_comp,
        S.comp_id_left, hg]⟩ : {f : S.Emb A B // S.range f = p}))
    ⟨fun _ _ h => cancel g (congrArg Subtype.val h), by
      intro f
      obtain ⟨e, he⟩ := factor f.val g (f.property.trans hg.symm)
      exact ⟨e, Subtype.ext he⟩⟩).symm

/-- Postcomposition maps a range fibre onto the whole fibre over the
transported copy. -/
theorem embeddingFibre_postcomp_surjective
    (factor : ∀ {B} (f g : S.Emb A B), S.range f = S.range g →
      ∃ e : S.Emb A A, S.compEmb e g = f)
    (full : ∀ f : S.Emb A A, S.range f = S.range (S.idEmb A))
    {B C : S.Obj} (f : S.Emb B C) (p : S.Copy A B) :
    Surjective (fun e : {e : S.Emb A B // S.range e = p} =>
      (⟨S.compEmb e.val f, (S.range_comp _ _).trans (congrArg (S.mapCopy f) e.property)⟩ :
        {e : S.Emb A C // S.range e = S.mapCopy f p})) := by
  intro e
  obtain ⟨g, hg⟩ := S.range_surjective p
  obtain ⟨a, ha⟩ := factor e.val (S.compEmb g f) (by rw [S.range_comp, hg, e.property])
  refine ⟨⟨S.compEmb a g, by rw [S.range_comp, full a, ← S.range_comp,
    S.comp_id_left, hg]⟩, Subtype.ext ?_⟩
  exact (S.comp_assoc a g f).trans ha

end SuccessorTree.FiniteCopySystem
