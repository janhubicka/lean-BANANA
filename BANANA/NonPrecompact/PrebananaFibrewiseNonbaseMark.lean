import BANANA.NonPrecompact.PrebananaFibrewiseAllocation

/-!
# Marking of non-distinguished fibres in a base-compatible allocation

The explicit fibrewise allocation fixes a base projection: witnesses
return to their target atoms, while unselected leaves are assigned
to a chosen target atom over their *own* base atom.

Consequently, if b is not the distinguished target atom over its
base, the only source leaf allocated to b is its chosen witness.
Its fibre therefore has the required mark.

The distinguished bins require an additional per-base parity
cancellation. A global total-parity assumption alone would be
insufficient: the cancellation must occur separately over each
base atom. The full finite-extension theorem is not claimed here.
-/

namespace SuccessorTree.NonPrecompact

/-- A non-distinguished bin has precisely its selected witness
as a preimage under the base-compatible allocation. -/
theorem prebananaFibrewiseAllocate_nonbase
    {α β δ : Type*} [Nonempty β]
    (source : α → δ) (target : β → δ)
    (witness : β → α)
    (hinj : Function.Injective witness)
    (hcompat : ∀ b : β, source (witness b) = target b)
    (base : δ → β) (hbase : ∀ a, target (base a) = a)
    (b : β) (hb : b ≠ base (target b))
    (x : α) (hx : prebananaFibrewiseAllocate source witness base x = b) :
    x = witness b := by
  classical
  by_cases hr : x ∈ Set.range witness
  · obtain ⟨b', rfl⟩ := hr
    rw [prebananaFibrewiseAllocate_witness source witness hinj base] at hx
    exact congrArg witness hx
  · have hs := prebananaFibrewiseAllocate_commutes
      source target witness hinj hcompat base hbase x
    rw [hx] at hs
    have hd : base (source x) = b := by
      simpa [prebananaFibrewiseAllocate, hr] using hx
    rw [hs] at hd
    exact False.elim (hb hd.symm)

/-- Every non-distinguished base fibre has the prescribed target mark. -/
theorem prebananaFibrewiseAllocate_nonbase_mark
    {α β δ : Type*} [Fintype α] [Nonempty β] [DecidableEq β]
    (source : α → δ) (target : β → δ)
    (markA : α → F2) (markB : β → F2)
    (witness : β → α) (hinj : Function.Injective witness)
    (hcompat : ∀ b : β, source (witness b) = target b)
    (hmark : ∀ b : β, markA (witness b) = markB b)
    (base : δ → β) (hbase : ∀ a, target (base a) = a)
    (b : β) (hb : b ≠ base (target b)) :
    (∑ x : α,
      if prebananaFibrewiseAllocate source witness base x = b
      then markA x else 0) = markB b := by
  classical
  have hz : ∀ x : α, x ≠ witness b →
      (if prebananaFibrewiseAllocate source witness base x = b
       then markA x else 0) = 0 := by
    intro x hx
    by_cases hxb : prebananaFibrewiseAllocate source witness base x = b
    · exact False.elim
        (hx (prebananaFibrewiseAllocate_nonbase
          source target witness hinj hcompat base hbase b hb x hxb))
    · simp [hxb]
  calc
    (∑ x : α,
      if prebananaFibrewiseAllocate source witness base x = b
      then markA x else 0) =
        (if prebananaFibrewiseAllocate source witness base (witness b) = b
         then markA (witness b) else 0) :=
           Fintype.sum_eq_single (witness b) (fun x hx => hz x hx)
    _ = markB b := by
          rw [prebananaFibrewiseAllocate_witness source witness hinj base b]
          simp [hmark]

end SuccessorTree.NonPrecompact
