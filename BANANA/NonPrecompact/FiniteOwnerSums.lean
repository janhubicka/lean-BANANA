import Mathlib

/-!
# Finite sums regrouped by total and partial atom owners

A total owner map assigns every source atom to one target label.
A partial owner map uses `Option`: `none` denotes an unused atom.
The two sum identities work over any commutative additive monoid.

The unital Boolean-algebra embeddings of pre-BANANA use total owners;
the non-unital Boolean-ring embeddings of Folkman–BANANA use partial
owners. The distinction is retained rather than hidden behind a
false equivalence of the embedding notions.
-/

namespace SuccessorTree.NonPrecompact

/-- Sum weights by every total-owner fibre, without losing any atom. -/
theorem finiteTotalOwner_sum_fibres
    {α β R : Type*} [Fintype α] [Fintype β]
    [DecidableEq β] [AddCommMonoid R]
    (owner : α → β) (weight : α → R) :
    (∑ b : β, ∑ x : α, if owner x = b then weight x else 0) =
      ∑ x : α, weight x := by
  classical
  rw [Finset.sum_comm]
  simp

/-- Sum the fibres of a partial owner, discarding exactly the unused atoms. -/
theorem finitePartialOwner_sum_fibres
    {α β R : Type*} [Fintype α] [Fintype β]
    [DecidableEq β] [AddCommMonoid R]
    (owner : α → Option β) (weight : α → R) :
    (∑ b : β, ∑ x : α, if owner x = some b then weight x else 0) =
      ∑ x : α, if owner x = none then 0 else weight x := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  cases h : owner x with
  | none => simp [h]
  | some b => simp [h]

end SuccessorTree.NonPrecompact
