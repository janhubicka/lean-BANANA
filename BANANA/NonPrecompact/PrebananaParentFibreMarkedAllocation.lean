import BANANA.NonPrecompact.PrebananaArbitraryTargetSuffixes
import BANANA.NonPrecompact.PrebananaMarkedAllocation

/-!
# Marked allocation below a nonempty finite fibre of existing atoms

An atom in a previously embedded Boolean algebra may contain
several word atoms of the current five-ary stage. It is therefore
not enough to refine only a single parent.

Given a nonempty finite family of parent atoms and nonempty finite
target atoms, suppose the total F₂ marking of the parent family
equals the total prescribed marking of the target family.
Refine *every* parent by k=|target| digits. Place all distinguished
target witnesses below one chosen parent, and send the remaining
descendants to a base target atom. The total descendant marking
and the witness-allocation parity lemma establish the marks of
all target fibres.

This is the finite-fibre partition construction, not yet the
simultaneous assembly of such partitions into a Boolean embedding
commuting with two prescribed maps.
-/

namespace SuccessorTree.NonPrecompact

/-- A nonempty finite marked family of existing atoms can be
refined at a uniform depth into any nonempty finite target family
with the same total F₂ mark, using nonempty correctly marked bins. -/
theorem prebananaParentFibre_markedAllocation
    (δ β : Type*) [Fintype δ] [Fintype β]
    [Nonempty δ] [Nonempty β] [DecidableEq β]
    (markD : δ → F2) (markB : β → F2)
    (htotal : (∑ d : δ, markD d) = ∑ b : β, markB b) :
    ∃ part : (δ × PrebananaFiveAryWord (Fintype.card β)) → β,
      Function.Surjective part ∧
        ∀ b : β,
          (∑ x : δ × PrebananaFiveAryWord (Fintype.card β),
            if part x = b then
              prebananaFiveAryDescendantMark
                (markD x.1) (Fintype.card β) x.2
            else 0) = markB b := by
  classical
  let parent : δ := Classical.choice (inferInstance : Nonempty δ)
  let witness : β → δ × PrebananaFiveAryWord (Fintype.card β) :=
    fun b => (parent, prebananaTargetSuffix β markB b)
  let base : β := Classical.choice (inferInstance : Nonempty β)
  let part := prebananaAllocateWitnesses witness base
  have hinj : Function.Injective witness := by
    intro b c h
    apply prebananaTargetSuffix_injective β markB
    exact congrArg Prod.snd h
  have hwitness : ∀ b : β,
      prebananaFiveAryDescendantMark
        (markD (witness b).1) (Fintype.card β) (witness b).2 =
          markB b := by
    intro b
    exact prebananaTargetSuffix_mark β markB (markD parent) b
  have hsum :
      (∑ x : δ × PrebananaFiveAryWord (Fintype.card β),
        prebananaFiveAryDescendantMark
          (markD x.1) (Fintype.card β) x.2) =
        ∑ b : β, markB b := by
    calc
      (∑ x : δ × PrebananaFiveAryWord (Fintype.card β),
        prebananaFiveAryDescendantMark
          (markD x.1) (Fintype.card β) x.2) =
        ∑ d : δ, ∑ w : PrebananaFiveAryWord (Fintype.card β),
          prebananaFiveAryDescendantMark (markD d)
            (Fintype.card β) w := by
              rw [Fintype.sum_prod_type]
      _ = ∑ d : δ, markD d := by
        apply Finset.sum_congr rfl
        intro d hd
        exact prebananaFiveAryDescendantMark_total
          (markD d) (Fintype.card β)
      _ = ∑ b : β, markB b := htotal
  refine ⟨part, prebananaAllocateWitnesses_surjective witness hinj base, ?_⟩
  intro b
  exact prebananaWitnessAllocation_preserves_mark
    (fun x : δ × PrebananaFiveAryWord (Fintype.card β) =>
      prebananaFiveAryDescendantMark (markD x.1)
        (Fintype.card β) x.2)
    markB witness hinj hwitness hsum base b

end SuccessorTree.NonPrecompact
