import BANANA.NonPrecompact.PrebananaAbstractCodeParity

/-!
# Boolean algebra operations in finite abstract atom codes

The canonical finite atom code respects zero, unit, binary joins
and binary meets. These facts are independent of the additive
pre-BANANA marking. Together with the verified parity theorem,
they form the Boolean-map interface used when transporting
the concrete powerset strong amalgam to arbitrary finite
Boolean algebras.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical

/-- The least element has empty atom-code support. -/
theorem prebananaAbstractBooleanCode_bot
    (α : Type*) [BooleanAlgebra α] [Fintype α] :
    prebananaAbstractBooleanCode α (⊥ : α) = ∅ := by
  classical
  simp [prebananaAbstractBooleanCode]

/-- The greatest element contains every atom index. -/
theorem prebananaAbstractBooleanCode_top
    (α : Type*) [BooleanAlgebra α] [Fintype α] :
    prebananaAbstractBooleanCode α (⊤ : α) = Finset.univ := by
  classical
  let e := prebananaFiniteBooleanAtomFinsetOrderIso α
  let a := prebananaAbstractAtomIndex α
  change ((e (⊤ : α)).image a.symm) = Finset.univ
  rw [e.map_top]
  ext i
  constructor
  · intro _
    exact Finset.mem_univ i
  · intro _
    exact Finset.mem_image.mpr
      ⟨a i, Finset.mem_univ _, a.symm_apply_apply i⟩

/-- Joins become unions of abstract-atom index sets. -/
theorem prebananaAbstractBooleanCode_sup
    (α : Type*) [BooleanAlgebra α] [Fintype α]
    (x y : α) :
    prebananaAbstractBooleanCode α (x ⊔ y) =
      prebananaAbstractBooleanCode α x ∪
      prebananaAbstractBooleanCode α y := by
  classical
  let e := prebananaFiniteBooleanAtomFinsetOrderIso α
  let a := prebananaAbstractAtomIndex α
  change ((e (x ⊔ y)).image a.symm) =
    ((e x).image a.symm) ∪ ((e y).image a.symm)
  rw [e.map_sup, Finset.image_union]

/-- Meets become intersections of abstract-atom index sets. -/
theorem prebananaAbstractBooleanCode_inf
    (α : Type*) [BooleanAlgebra α] [Fintype α]
    (x y : α) :
    prebananaAbstractBooleanCode α (x ⊓ y) =
      prebananaAbstractBooleanCode α x ∩
      prebananaAbstractBooleanCode α y := by
  classical
  let e := prebananaFiniteBooleanAtomFinsetOrderIso α
  let a := prebananaAbstractAtomIndex α
  change ((e (x ⊓ y)).image a.symm) =
    ((e x).image a.symm) ∩ ((e y).image a.symm)
  rw [e.map_inf]
  exact Finset.image_inter _ _ a.symm.injective

end SuccessorTree.NonPrecompact
