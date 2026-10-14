import BANANA.NonPrecompact.PrebananaFiniteBooleanModelHeredity

/-!
# Identity and composition of finite marked Boolean embeddings

A countable tower of finite pre-BANANA structures requires
composable embeddings. These elementary maps preserve the complete
Boolean functional language and the admissible F₂ marking.

No category-theoretic infrastructure or Fraïssé limit is assumed.
The underlying map is definitionally the identity or composition.
-/

namespace SuccessorTree.NonPrecompact

namespace PrebananaFiniteBooleanEmbedding

/-- Identity embedding of a finite marked Boolean algebra. -/
def id (A : PrebananaFiniteBooleanModel) :
    PrebananaFiniteBooleanEmbedding A A where
  hom := {
    toFun := fun x => x
    map_bot' := rfl
    map_top' := rfl
    map_sup' := by intro x y; rfl
    map_inf' := by intro x y; rfl
  }
  injective := by intro x y h; exact h
  preserves_μ := by intro x; rfl

/-- Composition of two marking-preserving Boolean embeddings. -/
def comp {A B C : PrebananaFiniteBooleanModel}
    (g : PrebananaFiniteBooleanEmbedding B C)
    (f : PrebananaFiniteBooleanEmbedding A B) :
    PrebananaFiniteBooleanEmbedding A C where
  hom := {
    toFun := fun x => g.hom (f.hom x)
    map_bot' := by
      change g.hom (f.hom (⊥ : A.carrier)) = (⊥ : C.carrier)
      rw [map_bot f.hom, map_bot g.hom]
    map_top' := by
      change g.hom (f.hom (⊤ : A.carrier)) = (⊤ : C.carrier)
      rw [map_top f.hom, map_top g.hom]
    map_sup' := by
      intro x y
      change g.hom (f.hom (x ⊔ y)) =
        g.hom (f.hom x) ⊔ g.hom (f.hom y)
      rw [map_sup f.hom, map_sup g.hom]
    map_inf' := by
      intro x y
      change g.hom (f.hom (x ⊓ y)) =
        g.hom (f.hom x) ⊓ g.hom (f.hom y)
      rw [map_inf f.hom, map_inf g.hom]
  }
  injective := by
    intro x y h
    exact f.injective (g.injective h)
  preserves_μ := by
    intro x
    exact (g.preserves_μ (f.hom x)).trans (f.preserves_μ x)

/-- The composite embedding acts by the composite carrier map. -/
theorem comp_apply {A B C : PrebananaFiniteBooleanModel}
    (g : PrebananaFiniteBooleanEmbedding B C)
    (f : PrebananaFiniteBooleanEmbedding A B)
    (x : A.carrier) :
    (g.comp f).hom x = g.hom (f.hom x) := rfl

/-- Identity is neutral on the left, pointwise. -/
theorem id_comp_apply {A B : PrebananaFiniteBooleanModel}
    (f : PrebananaFiniteBooleanEmbedding A B) (x : A.carrier) :
    ((id B).comp f).hom x = f.hom x := rfl

/-- Identity is neutral on the right, pointwise. -/
theorem comp_id_apply {A B : PrebananaFiniteBooleanModel}
    (f : PrebananaFiniteBooleanEmbedding A B) (x : A.carrier) :
    (f.comp (id A)).hom x = f.hom x := rfl

/-- Triple composites agree pointwise. -/
theorem comp_assoc_apply {A B C D : PrebananaFiniteBooleanModel}
    (f : PrebananaFiniteBooleanEmbedding A B)
    (g : PrebananaFiniteBooleanEmbedding B C)
    (h : PrebananaFiniteBooleanEmbedding C D)
    (x : A.carrier) :
    ((h.comp g).comp f).hom x =
      (h.comp (g.comp f)).hom x := rfl

end PrebananaFiniteBooleanEmbedding

end SuccessorTree.NonPrecompact
