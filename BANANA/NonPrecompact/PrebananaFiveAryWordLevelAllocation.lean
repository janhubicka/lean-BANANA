import BANANA.NonPrecompact.PrebananaFiveAryRefinementAllocation
import BANANA.NonPrecompact.PrebananaFiveAryConcatenation

/-!
# A marked allocation on actual five-ary word levels

The simultaneous refinement theorem constructs an atom allocation
on (old word, suffix) pairs. Mathlib's `Fin.appendEquiv` identifies
those pairs with the actual words at level n+k. This file transports
the allocation through that equivalence, checking the F₂ marking
with the independently proved concatenation identity.

The result has the correct atom-level data for a finite-extension
embedding: surjectivity, exact compatibility with the original
base-atom projection, and preservation of the prescribed mark on
every target atom. Turning its inverse-image operation on subsets
into a fully typed marked Boolean-algebra embedding and proving
the commuting square are separate obligations.
-/

namespace SuccessorTree.NonPrecompact

/-- Simultaneous finite refinement of a marked stage-n word partition
to a marked target atom family, realised on *actual* stage-(n+k)
words with k equal to the number of target atoms. -/
theorem prebananaFiveAryWordLevel_markedAllocation
    (n : ℕ) (β δ : Type*) [Fintype β]
    [DecidableEq β] [DecidableEq δ] [Nonempty β]
    (source : PrebananaFiveAryWord n → δ)
    (target : β → δ)
    (hsource : Function.Surjective source)
    (htarget : Function.Surjective target)
    (markB : β → F2)
    (hlocal : ∀ d : δ,
      (∑ w : PrebananaFiveAryWord n,
        if source w = d then prebananaFiveAryWordMark n w else 0) =
      ∑ b : β, if target b = d then markB b else 0) :
    ∃ part :
      PrebananaFiveAryWord (n + Fintype.card β) → β,
      Function.Surjective part ∧
      (∀ w,
        target (part w) =
          source ((Fin.appendEquiv n (Fintype.card β)).symm w).1) ∧
      (∀ b : β,
        (∑ w : PrebananaFiveAryWord (n + Fintype.card β),
          if part w = b then
            prebananaFiveAryWordMark (n + Fintype.card β) w
          else 0) = markB b) := by
  classical
  let k : ℕ := Fintype.card β
  obtain ⟨alloc, hsurj, hcomm, hmark⟩ :=
    prebananaFiveAryRefinement_markedAllocation
      (PrebananaFiveAryWord n) β δ source target
      hsource htarget (prebananaFiveAryWordMark n) markB hlocal
  let e :
      (PrebananaFiveAryWord n × PrebananaFiveAryWord k) ≃
        PrebananaFiveAryWord (n + k) := Fin.appendEquiv n k
  let part : PrebananaFiveAryWord (n + k) → β :=
    fun w => alloc (e.symm w)
  have hpartSurj : Function.Surjective part := by
    intro b
    obtain ⟨p, hp⟩ := hsurj b
    refine ⟨e p, ?_⟩
    simpa [part] using hp
  have hpartComm (w : PrebananaFiveAryWord (n + k)) :
      target (part w) = source (e.symm w).1 :=
    hcomm (e.symm w)
  have hword (p : PrebananaFiveAryWord n × PrebananaFiveAryWord k) :
      prebananaFiveAryWordMark (n + k) (e p) =
        prebananaFiveAryDescendantMark
          (prebananaFiveAryWordMark n p.1) k p.2 := by
    simpa [e] using prebananaFiveAryWordMark_append n k p.1 p.2
  have hpartMark (b : β) :
      (∑ w : PrebananaFiveAryWord (n + k),
        if part w = b then prebananaFiveAryWordMark (n + k) w else 0) =
        markB b := by
    calc
      (∑ w : PrebananaFiveAryWord (n + k),
        if part w = b then prebananaFiveAryWordMark (n + k) w else 0) =
        ∑ p : PrebananaFiveAryWord n × PrebananaFiveAryWord k,
          if alloc p = b then prebananaFiveAryWordMark (n + k) (e p)
          else 0 := by
            exact (Fintype.sum_equiv e
              (fun p => if alloc p = b then
                prebananaFiveAryWordMark (n + k) (e p) else 0)
              (fun w => if part w = b then
                prebananaFiveAryWordMark (n + k) w else 0)
              (by intro p; simp [part])).symm
      _ = ∑ p : PrebananaFiveAryWord n × PrebananaFiveAryWord k,
          if alloc p = b then
            prebananaFiveAryDescendantMark
              (prebananaFiveAryWordMark n p.1) k p.2
          else 0 := by
            apply Finset.sum_congr rfl
            intro p hp
            by_cases h : alloc p = b
            · simp only [h, ite_true]
              exact hword p
            · simp [h]
      _ = markB b := hmark b
  exact ⟨part, hpartSurj, hpartComm, hpartMark⟩

end SuccessorTree.NonPrecompact
