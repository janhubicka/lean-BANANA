import BANANA.NonPrecompact.PrebananaMarkedNonbaseFibres
import BANANA.NonPrecompact.FiniteOwnerSums

/-!
# All fibres of the finite witness allocation preserve marking

Once one distinct source leaf of the correct mark has been selected
for every target atom, the allocation map sends all unselected
leaves to a distinguished bin. The other bins have exactly their
selected leaf, hence their target mark.

If total source marking agrees with total target marking, the
distinguished bin also has the correct mark: partition the source
sum by allocation fibres and cancel the equal contribution from
all other target atoms.

This is the complete marking certificate for an already supplied
injection of witnesses. Constructing witnesses compatible with a
particular finite extension and proving the commuting square
remain separate obligations.
-/

namespace SuccessorTree.NonPrecompact

/-- Every fibre of the witness allocation has precisely its
prescribed F₂ marking, provided total source and target markings
agree. -/
theorem prebananaWitnessAllocation_preserves_mark
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (markA : α → F2) (markB : β → F2)
    (witness : β → α) (hinj : Function.Injective witness)
    (hmark : ∀ b : β, markA (witness b) = markB b)
    (htotal : (∑ x : α, markA x) = ∑ b : β, markB b)
    (base b : β) :
    (∑ x : α,
      if prebananaAllocateWitnesses witness base x = b
      then markA x else 0) = markB b := by
  classical
  by_cases hb : b = base
  · subst b
    let F : β → F2 := fun y =>
      ∑ x : α,
        if prebananaAllocateWitnesses witness base x = y
        then markA x else 0
    have hdecomp : (∑ y : β, F y) = ∑ x : α, markA x := by
      exact finiteTotalOwner_sum_fibres
        (prebananaAllocateWitnesses witness base) markA
    have hrest :
        (∑ y ∈ (Finset.univ : Finset β).erase base, F y) =
        ∑ y ∈ (Finset.univ : Finset β).erase base, markB y := by
      apply Finset.sum_congr rfl
      intro y hy
      exact prebananaWitnessAllocation_nonbaseMark
        markA markB witness hinj hmark base y
        (Finset.ne_of_mem_erase hy)
    have hsplit :
        (∑ y ∈ (Finset.univ : Finset β).erase base, F y) + F base =
        (∑ y ∈ (Finset.univ : Finset β).erase base, markB y) +
          markB base := by
      calc
        (∑ y ∈ (Finset.univ : Finset β).erase base, F y) + F base =
          ∑ y : β, F y :=
            Finset.sum_erase_add Finset.univ F (Finset.mem_univ base)
        _ = ∑ x : α, markA x := hdecomp
        _ = ∑ y : β, markB y := htotal
        _ = (∑ y ∈ (Finset.univ : Finset β).erase base, markB y) +
            markB base :=
          (Finset.sum_erase_add Finset.univ markB
            (Finset.mem_univ base)).symm
    rw [hrest] at hsplit
    exact add_left_cancel hsplit
  · exact prebananaWitnessAllocation_nonbaseMark
      markA markB witness hinj hmark base b hb

end SuccessorTree.NonPrecompact
