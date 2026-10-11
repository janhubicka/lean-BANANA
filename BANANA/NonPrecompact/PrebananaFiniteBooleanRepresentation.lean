import BANANA.NonPrecompact.PrebananaPowersetStrongAmalgam
import Mathlib.Data.Fintype.Order
import Mathlib.Order.Atoms

/-!
# Finite Boolean algebras as powersets of their atoms

This is the representation interface between the abstract Boolean
algebras used in the pre-BANANA manuscript and the atom-coordinate
Lean implementation.

Mathlib supplies both the canonical representation theorem for
complete atomic Boolean algebras and the finite completeness
construction. This module combines them without additional axioms.

The induced marking from a Boolean-algebra parity map and the
translation of arbitrary unital embeddings remain separate steps.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical

/-- Atoms of an arbitrary Boolean algebra, as a subtype. -/
abbrev PrebananaAbstractAtoms (α : Type*) [BooleanAlgebra α] :=
  {a : α // IsAtom a}

/-- An arbitrary finite Boolean algebra is order-isomorphic to
the set of subsets of its atoms. -/
noncomputable def prebananaFiniteBooleanAtomSetOrderIso
    (α : Type*) [BooleanAlgebra α] [Fintype α] :
    α ≃o Set (PrebananaAbstractAtoms α) := by
  letI : CompleteAtomicBooleanAlgebra α :=
    Fintype.toCompleteAtomicBooleanAlgebra α
  exact CompleteAtomicBooleanAlgebra.toSetOfIsAtom

/-- The representation of an element is precisely its set of
atoms lying beneath it. -/
theorem prebananaFiniteBooleanAtomSet_mem_iff
    (α : Type*) [BooleanAlgebra α] [Fintype α]
    (x : α) (a : PrebananaAbstractAtoms α) :
    a ∈ prebananaFiniteBooleanAtomSetOrderIso α x ↔
      (a : α) ≤ x := by
  rfl

/-- The finite powerset representation, with finite subsets
rather than arbitrary sets. -/
noncomputable def prebananaFiniteBooleanAtomFinsetEquiv
    (α : Type*) [BooleanAlgebra α] [Fintype α] :
    α ≃ Finset (PrebananaAbstractAtoms α) := by
  classical
  let e := prebananaFiniteBooleanAtomSetOrderIso α
  refine {
    toFun := fun x => (e x).toFinset
    invFun := fun s => e.symm (s : Set (PrebananaAbstractAtoms α))
    left_inv := ?_
    right_inv := ?_
  }
  · intro x
    change e.symm ((e x).toFinset : Set (PrebananaAbstractAtoms α)) = x
    simp
  · intro s
    change (e (e.symm (s : Set (PrebananaAbstractAtoms α)))).toFinset = s
    simp

/-- The stronger order isomorphism to finite atom subsets.
All Boolean operations may be transported through this order isomorphism. -/
noncomputable def prebananaFiniteBooleanAtomFinsetOrderIso
    (α : Type*) [BooleanAlgebra α] [Fintype α] :
    α ≃o Finset (PrebananaAbstractAtoms α) :=
  (prebananaFiniteBooleanAtomSetOrderIso α).trans
    ((Fintype.finsetOrderIsoSet :
      Finset (PrebananaAbstractAtoms α) ≃o
        Set (PrebananaAbstractAtoms α)).symm)

/-- The finite-atom order isomorphism preserves joins (unions). -/
theorem prebananaFiniteBooleanAtomFinsetOrderIso_sup
    (α : Type*) [BooleanAlgebra α] [Fintype α]
    (x y : α) :
    prebananaFiniteBooleanAtomFinsetOrderIso α (x ⊔ y) =
      prebananaFiniteBooleanAtomFinsetOrderIso α x ∪
      prebananaFiniteBooleanAtomFinsetOrderIso α y := by
  change prebananaFiniteBooleanAtomFinsetOrderIso α (x ⊔ y) =
    prebananaFiniteBooleanAtomFinsetOrderIso α x ⊔
    prebananaFiniteBooleanAtomFinsetOrderIso α y
  exact (prebananaFiniteBooleanAtomFinsetOrderIso α).map_sup x y

/-- The finite-atom order isomorphism preserves meets (intersections). -/
theorem prebananaFiniteBooleanAtomFinsetOrderIso_inf
    (α : Type*) [BooleanAlgebra α] [Fintype α]
    (x y : α) :
    prebananaFiniteBooleanAtomFinsetOrderIso α (x ⊓ y) =
      prebananaFiniteBooleanAtomFinsetOrderIso α x ∩
      prebananaFiniteBooleanAtomFinsetOrderIso α y := by
  change prebananaFiniteBooleanAtomFinsetOrderIso α (x ⊓ y) =
    prebananaFiniteBooleanAtomFinsetOrderIso α x ⊓
    prebananaFiniteBooleanAtomFinsetOrderIso α y
  exact (prebananaFiniteBooleanAtomFinsetOrderIso α).map_inf x y

/-- The abstract element corresponding to a finite collection
of atoms is uniquely recovered from that collection. -/
theorem prebananaFiniteBooleanAtomFinsetEquiv_injective
    (α : Type*) [BooleanAlgebra α] [Fintype α] :
    Function.Injective
      (prebananaFiniteBooleanAtomFinsetEquiv α) :=
  (prebananaFiniteBooleanAtomFinsetEquiv α).injective

end SuccessorTree.NonPrecompact
