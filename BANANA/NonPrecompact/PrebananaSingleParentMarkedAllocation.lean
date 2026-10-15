import BANANA.NonPrecompact.PrebananaArbitraryTargetSuffixes
import BANANA.NonPrecompact.PrebananaMarkedAllocation

/-!
# A marked partition of the descendants of one five-ary parent

A finite collection of desired target atoms can be assigned to
the descendants of one parent provided the sum of their F₂ marks
equals the parent's mark. The depth is the number of target atoms.

One distinct, correctly marked suffix is selected for each target
atom; the other suffixes are allocated to a distinguished atom.
The total descendant-mark identity ensures that the latter fibre
has the correct mark as well.

This is the local allocation theorem. The compatibility of the
partitions belonging to different existing atoms and the resulting
commuting Boolean-embedding diagram are separate obligations.
-/

namespace SuccessorTree.NonPrecompact

/-- Every nonempty finite family of prescribed target atoms whose
marks sum to a parent mark admits a surjective, marked allocation
of all descendants at depth equal to the number of target atoms. -/
theorem prebananaSingleParent_markedAllocation
    (β : Type*) [Fintype β] [Nonempty β] [DecidableEq β]
    (p : F2) (markB : β → F2)
    (htotal : (∑ b : β, markB b) = p) :
    ∃ part : PrebananaFiveAryWord (Fintype.card β) → β,
      Function.Surjective part ∧
        ∀ b : β,
          (∑ w : PrebananaFiveAryWord (Fintype.card β),
            if part w = b then
              prebananaFiveAryDescendantMark p (Fintype.card β) w
            else 0) = markB b := by
  classical
  let witness : β → PrebananaFiveAryWord (Fintype.card β) :=
    prebananaTargetSuffix β markB
  let base : β := Classical.choice (inferInstance : Nonempty β)
  let part := prebananaAllocateWitnesses witness base
  have hinj : Function.Injective witness :=
    prebananaTargetSuffix_injective β markB
  have hwitness : ∀ b : β,
      prebananaFiveAryDescendantMark p (Fintype.card β)
        (witness b) = markB b := by
    intro b
    exact prebananaTargetSuffix_mark β markB p b
  have hsum :
      (∑ w : PrebananaFiveAryWord (Fintype.card β),
        prebananaFiveAryDescendantMark p (Fintype.card β) w) =
        ∑ b : β, markB b :=
    (prebananaFiveAryDescendantMark_total p (Fintype.card β)).trans
      htotal.symm
  refine ⟨part, prebananaAllocateWitnesses_surjective witness hinj base, ?_⟩
  intro b
  exact prebananaWitnessAllocation_preserves_mark
    (prebananaFiveAryDescendantMark p (Fintype.card β))
    markB witness hinj hwitness hsum base b

end SuccessorTree.NonPrecompact
