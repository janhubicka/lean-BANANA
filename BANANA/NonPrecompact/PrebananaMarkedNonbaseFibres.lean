import BANANA.NonPrecompact.PrebananaWitnessAllocation

/-!
# The parity of non-distinguished witness-allocation fibres

Given one different witness atom for each target atom, with the
witness's F₂ mark equal to the corresponding target mark, assign
unselected leaves to a distinguished bin. Every *other* bin has
exactly one atom and therefore automatically has the correct mark.

The distinguished bin may also receive unused leaves. Its parity
must be deduced separately from matching total markings; this
module does not yet claim the complete marked partition.
-/

namespace SuccessorTree.NonPrecompact

/-- Every non-distinguished fibre of the witness retraction has
the prescribed F₂ mark. -/
theorem prebananaWitnessAllocation_nonbaseMark
    {α β : Type*} [Fintype α] [DecidableEq β]
    (markA : α → F2) (markB : β → F2)
    (witness : β → α) (hinj : Function.Injective witness)
    (hmark : ∀ b : β, markA (witness b) = markB b)
    (base b : β) (hb : b ≠ base) :
    (∑ x : α,
      if prebananaAllocateWitnesses witness base x = b
      then markA x else 0) = markB b := by
  classical
  have hzero : ∀ x : α, x ≠ witness b →
      (if prebananaAllocateWitnesses witness base x = b
       then markA x else 0) = 0 := by
    intro x hx
    by_cases hbin : prebananaAllocateWitnesses witness base x = b
    · exact False.elim
        (hx (prebananaAllocateWitnesses_nonbase
          witness hinj base b hb x hbin))
    · simp [hbin]
  calc
    (∑ x : α,
      if prebananaAllocateWitnesses witness base x = b
      then markA x else 0) =
        (if prebananaAllocateWitnesses witness base (witness b) = b
         then markA (witness b) else 0) :=
           Fintype.sum_eq_single (witness b) (fun x hx => hzero x hx)
    _ = markB b := by
          rw [prebananaAllocateWitnesses_witness witness hinj base b]
          simp [hmark]

end SuccessorTree.NonPrecompact
