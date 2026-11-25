import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Hom.Bounded

/-!
# Finite and countable marked Boolean models

The finite language consists of the bounded lattice operations and a
disjoint-additive binary marking. The definitions are independent of
any concrete cylinder presentation.
-/

namespace SuccessorTree.NonPrecompact

/-- A nontrivial finite Boolean algebra equipped with an admissible
disjoint-additive parity marking. -/
structure PrebananaFiniteBooleanModel where
  carrier : Type
  [booleanAlgebra : BooleanAlgebra carrier]
  [finite : Fintype carrier]
  [nontrivial : Nontrivial carrier]
  μ : carrier → ZMod 2
  μ_bot : μ ⊥ = 0
  μ_top : μ ⊤ = 0
  μ_add : ∀ x y : carrier, x ⊓ y = ⊥ →
    μ (x ⊔ y) = μ x + μ y

attribute [instance] PrebananaFiniteBooleanModel.booleanAlgebra
  PrebananaFiniteBooleanModel.finite
  PrebananaFiniteBooleanModel.nontrivial

/-- A marking-preserving embedding of arbitrary finite
Boolean–BANANA Boolean algebras. -/
structure PrebananaFiniteBooleanEmbedding
    (A B : PrebananaFiniteBooleanModel) where
  hom : BoundedLatticeHom A.carrier B.carrier
  injective : Function.Injective hom
  preserves_μ : ∀ x : A.carrier, B.μ (hom x) = A.μ x

/-- A countable, nontrivial Boolean algebra with an admissible
disjoint-additive F₂ marking. -/
structure PrebananaCountableBooleanModel where
  carrier : Type
  [booleanAlgebra : BooleanAlgebra carrier]
  [countable : Countable carrier]
  [nontrivial : Nontrivial carrier]
  μ : carrier → ZMod 2
  μ_bot : μ ⊥ = 0
  μ_top : μ ⊤ = 0
  μ_add : ∀ x y : carrier, x ⊓ y = ⊥ →
    μ (x ⊔ y) = μ x + μ y

attribute [instance] PrebananaCountableBooleanModel.booleanAlgebra
  PrebananaCountableBooleanModel.countable
  PrebananaCountableBooleanModel.nontrivial

/-- An actual marked embedding from an arbitrary finite
pre-BANANA algebra into a countable marked Boolean algebra. -/
structure PrebananaFiniteToCountableEmbedding
    (A : PrebananaFiniteBooleanModel)
    (M : PrebananaCountableBooleanModel) where
  hom : BoundedLatticeHom A.carrier M.carrier
  injective : Function.Injective hom
  preserves_μ : ∀ x : A.carrier, M.μ (hom x) = A.μ x

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
