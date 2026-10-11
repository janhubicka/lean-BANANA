import BANANA.NonPrecompact.PrebananaAbstractParityDecomposition

/-!
# Actual abstract atoms in the canonical powerset representation

The inverse image of the singleton containing an abstract Boolean
atom is that atom itself. This connects the finite powerset
representation to the exact atom-marking formula in the circulation
manuscript, which evaluates the parity function at the atoms of
the original Boolean algebra.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical BigOperators

/-- The singleton of an abstract atom represents the atom itself
under the finite Boolean algebra to atom-powerset order isomorphism. -/
theorem prebananaFiniteBoolean_singleton_represents_atom
    (α : Type*) [BooleanAlgebra α] [Fintype α]
    (a : PrebananaAbstractAtoms α) :
    (prebananaFiniteBooleanAtomFinsetOrderIso α).symm
      ({a} : Finset (PrebananaAbstractAtoms α)) = (a : α) := by
  classical
  let e := prebananaFiniteBooleanAtomFinsetOrderIso α
  apply e.injective
  change e (e.symm ({a} : Finset (PrebananaAbstractAtoms α))) = e (a : α)
  rw [e.apply_symm_apply]
  ext b
  have hmem : b ∈ e (a : α) ↔ (b : α) ≤ (a : α) := by
    simpa [e, prebananaFiniteBooleanAtomFinsetOrderIso] using
      (prebananaFiniteBooleanAtomSet_mem_iff α (a : α) b)
  constructor
  · intro hb
    have hab : b = a := Finset.mem_singleton.mp hb
    exact hmem.mpr (hab ▸ le_rfl)
  · intro hb
    have hba : (b : α) ≤ (a : α) := hmem.mp hb
    have hbeq : (b : α) = (a : α) :=
      (a.property.le_iff_eq b.property.ne_bot).mp hba
    exact Finset.mem_singleton.mpr (Subtype.ext hbeq)

/-- Finite disjoint additivity is precisely the atom-sum formula
over atoms of the *original* Boolean algebra, not just powerset
representatives. -/
theorem prebananaAbstractParity_atomSum_on_atoms
    (α : Type*) [BooleanAlgebra α] [Fintype α]
    (μ : α → F2)
    (hzero : μ ⊥ = 0)
    (hadd : ∀ x y : α, x ⊓ y = ⊥ →
      μ (x ⊔ y) = μ x + μ y)
    (x : α) :
    μ x =
      ∑ a ∈ prebananaFiniteBooleanAtomFinsetOrderIso α x,
        μ (a : α) := by
  simpa only [prebananaFiniteBoolean_singleton_represents_atom] using
    (prebananaAbstractParity_atomSum α μ hzero hadd x)

/-- If the marking vanishes at the top, the sum of markings on
the actual abstract atoms is zero. -/
theorem prebananaAbstractParity_total_even_on_atoms
    (α : Type*) [BooleanAlgebra α] [Fintype α]
    (μ : α → F2)
    (hzero : μ ⊥ = 0)
    (htop : μ ⊤ = 0)
    (hadd : ∀ x y : α, x ⊓ y = ⊥ →
      μ (x ⊔ y) = μ x + μ y) :
    (∑ a : PrebananaAbstractAtoms α, μ (a : α)) = 0 := by
  simpa only [prebananaFiniteBoolean_singleton_represents_atom] using
    (prebananaAbstractParity_total_even α μ hzero htop hadd)

end SuccessorTree.NonPrecompact
