import BANANA.NonPrecompact.PrebananaFibrewiseNonbaseMark
import BANANA.NonPrecompact.PrebananaBaseMarkCompletion

/-!
# A complete base-compatible marked atom allocation

The finite-extension construction needs an atom allocation which is
simultaneously surjective, commutes with the projection to the old
base, and preserves each target atom's F₂ marking.

A compatible injective witness selection and equality of the marking
totals separately over every base atom are sufficient. Selected atoms
are allocated back to their targets; all unselected source atoms go
to a distinguished target in their own base fibre. The marking of
the distinguished target follows by cancellation *within that fibre*.

This theorem completes the abstract allocation certificate. It does
not choose witnesses from a concrete five-ary word tower, or itself
construct the associated unital Boolean embedding.
-/

namespace SuccessorTree.NonPrecompact

/-- The fibrewise witness allocation is simultaneously surjective,
base commuting, and marking preserving under exact per-base
compatibility of the total source and target markings. -/
theorem prebananaFibrewiseAllocate_marked
    {α β δ : Type*} [Fintype α] [Fintype β]
    [DecidableEq β] [DecidableEq δ] [Nonempty β]
    (source : α → δ) (target : β → δ)
    (markA : α → F2) (markB : β → F2)
    (witness : β → α) (hinj : Function.Injective witness)
    (hcompat : ∀ b : β, source (witness b) = target b)
    (hmark : ∀ b : β, markA (witness b) = markB b)
    (base : δ → β) (hbase : ∀ a : δ, target (base a) = a)
    (hlocal : ∀ a : δ,
      (∑ x : α, if source x = a then markA x else 0) =
        ∑ b : β, if target b = a then markB b else 0) :
    Function.Surjective (prebananaFibrewiseAllocate source witness base) ∧
      (∀ x : α, target (prebananaFibrewiseAllocate source witness base x) =
        source x) ∧
      (∀ b : β,
        (∑ x : α,
          if prebananaFibrewiseAllocate source witness base x = b
          then markA x else 0) = markB b) := by
  classical
  refine ⟨prebananaFibrewiseAllocate_surjective
    source witness hinj base, ?_, ?_⟩
  · intro x
    exact prebananaFibrewiseAllocate_commutes
      source target witness hinj hcompat base hbase x
  · intro b
    exact prebananaBaseMarkCompletion
      source target (prebananaFibrewiseAllocate source witness base)
      (prebananaFibrewiseAllocate_commutes
        source target witness hinj hcompat base hbase)
      markA markB base hbase hlocal
      (fun c hc => prebananaFibrewiseAllocate_nonbase_mark
        source target markA markB witness hinj hcompat hmark
        base hbase c hc) b

end SuccessorTree.NonPrecompact
