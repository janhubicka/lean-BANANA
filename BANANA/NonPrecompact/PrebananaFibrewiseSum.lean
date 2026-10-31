import BANANA.NonPrecompact.PrebananaResidualParity
import BANANA.NonPrecompact.FiniteOwnerSums

/-!
# Per-base sum identity for commuting atom projections

If a finite atom map f commutes with two projections to a common base,
then regrouping its source-atom markings by f preserves the total
marking separately above *each base atom*. Global parity alone does
not suffice for the local finite-extension argument.

This statement requires no injection or surjection hypothesis on f.
The proof uses the shared total-owner fibre-sum calculation, also used
by Folkman--BANANA in its partial-owner form.
-/

namespace SuccessorTree.NonPrecompact

/-- Regrouping a finite marked set by a map that preserves its base
projection leaves each individual base-fibre total unchanged. -/
theorem prebananaFibrewiseSum_identity
    {α β δ : Type*} [Fintype α] [Fintype β]
    [DecidableEq β] [DecidableEq δ]
    (source : α → δ) (target : β → δ) (f : α → β)
    (hcomm : ∀ x, target (f x) = source x)
    (mark : α → F2) (a : δ) :
    (∑ b : β, ∑ x : α,
      if target b = a ∧ f x = b then mark x else 0) =
    ∑ x : α, if source x = a then mark x else 0 := by
  classical
  calc
    (∑ b : β, ∑ x : α,
      if target b = a ∧ f x = b then mark x else 0) =
      ∑ b : β, ∑ x : α,
        if f x = b then (if source x = a then mark x else 0) else 0 := by
          apply Finset.sum_congr rfl
          intro b hb
          apply Finset.sum_congr rfl
          intro x hx
          by_cases hfb : f x = b
          · have hbase : target b = source x := by
              simpa [hfb] using hcomm x
            simp [hfb, hbase]
          · simp [hfb]
    _ = ∑ x : α, if source x = a then mark x else 0 :=
      finiteTotalOwner_sum_fibres f
        (fun x : α => if source x = a then mark x else 0)

end SuccessorTree.NonPrecompact
