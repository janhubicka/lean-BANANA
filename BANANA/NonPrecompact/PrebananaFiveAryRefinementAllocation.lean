import BANANA.NonPrecompact.PrebananaFibrewiseMarkedAllocation
import BANANA.NonPrecompact.PrebananaArbitraryTargetSuffixes
import BANANA.NonPrecompact.PrebananaFiveAryDescendantParity

/-!
# Simultaneous marked refinement over an arbitrary finite base

Fix an existing finite family of atoms `α`, a finite target atom
family `β` and an old base `δ`. Let `source : α → δ` and
`target : β → δ` be surjective atom projections whose F₂ markings
agree in **every** base fibre.

At the common refinement depth `Fintype.card β`, all descendants
of the old source atoms admit one marked, surjective allocation to
the target atoms which commutes with the base projections.

Select, for each target atom, a descendant beneath a chosen old
source atom over the same base atom. All target suffixes are globally
distinct by the explicit reset-letter construction; their marking
is independent of the chosen parent's marking. The remaining
descendants are assigned to a distinguished target atom within each
base fibre, and per-base parity completes the proof.

This is the global *atom allocation* for the finite-extension lemma.
Relating `α` to an actual set of level-n words, and transporting
the allocation through the word-concatenation equivalence to obtain
an embedding of complete Boolean stages, are separate steps.
-/

namespace SuccessorTree.NonPrecompact

/-- Every compatible finite diagram of marked atom projections has
a simultaneous marked, base-commuting refinement at the uniform
depth given by the target atom count. -/
theorem prebananaFiveAryRefinement_markedAllocation
    (α β δ : Type*) [Fintype α] [Fintype β]
    [DecidableEq β] [DecidableEq δ] [Nonempty β]
    (source : α → δ) (target : β → δ)
    (hsource : Function.Surjective source)
    (htarget : Function.Surjective target)
    (markA : α → F2) (markB : β → F2)
    (hlocal : ∀ d : δ,
      (∑ a : α, if source a = d then markA a else 0) =
        ∑ b : β, if target b = d then markB b else 0) :
    ∃ part :
      (α × PrebananaFiveAryWord (Fintype.card β)) → β,
      Function.Surjective part ∧
      (∀ x, target (part x) = source x.1) ∧
      (∀ b : β,
        (∑ x : α × PrebananaFiveAryWord (Fintype.card β),
          if part x = b then
            prebananaFiveAryDescendantMark
              (markA x.1) (Fintype.card β) x.2
          else 0) = markB b) := by
  classical
  let k : ℕ := Fintype.card β
  let parent : δ → α := fun d => Classical.choose (hsource d)
  have hparent (d : δ) : source (parent d) = d :=
    Classical.choose_spec (hsource d)
  let base : δ → β := fun d => Classical.choose (htarget d)
  have hbase (d : δ) : target (base d) = d :=
    Classical.choose_spec (htarget d)
  let witness : β → α × PrebananaFiveAryWord k :=
    fun b => (parent (target b), prebananaTargetSuffix β markB b)
  have hinj : Function.Injective witness := by
    intro b c h
    apply prebananaTargetSuffix_injective β markB
    exact congrArg Prod.snd h
  have hcompat (b : β) :
      source (witness b).1 = target b := hparent (target b)
  have hwitness (b : β) :
      prebananaFiveAryDescendantMark
        (markA (witness b).1) k (witness b).2 = markB b := by
    exact prebananaTargetSuffix_mark β markB
      (markA (parent (target b))) b
  have hrefined (d : δ) :
      (∑ x : α × PrebananaFiveAryWord k,
        if source x.1 = d then
          prebananaFiveAryDescendantMark (markA x.1) k x.2
        else 0) =
      ∑ b : β, if target b = d then markB b else 0 := by
    calc
      (∑ x : α × PrebananaFiveAryWord k,
        if source x.1 = d then
          prebananaFiveAryDescendantMark (markA x.1) k x.2
        else 0) =
          ∑ a : α, ∑ w : PrebananaFiveAryWord k,
            if source a = d then
              prebananaFiveAryDescendantMark (markA a) k w
            else 0 := by
              rw [Fintype.sum_prod_type]
      _ = ∑ a : α, if source a = d then markA a else 0 := by
        apply Finset.sum_congr rfl
        intro a ha
        by_cases h : source a = d
        · simp only [h, ite_true]
          exact prebananaFiveAryDescendantMark_total (markA a) k
        · simp [h]
      _ = ∑ b : β, if target b = d then markB b else 0 :=
        hlocal d
  let part : α × PrebananaFiveAryWord k → β :=
    prebananaFibrewiseAllocate
      (fun x : α × PrebananaFiveAryWord k => source x.1)
      witness base
  obtain ⟨hsurj, hcomm, hmark⟩ :=
    prebananaFibrewiseAllocate_marked
      (fun x : α × PrebananaFiveAryWord k => source x.1)
      target
      (fun x : α × PrebananaFiveAryWord k =>
        prebananaFiveAryDescendantMark (markA x.1) k x.2)
      markB witness hinj hcompat hwitness base hbase hrefined
  exact ⟨part, hsurj, hcomm, hmark⟩

end SuccessorTree.NonPrecompact
