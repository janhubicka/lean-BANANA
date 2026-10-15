import BANANA.NonPrecompact.PrebananaResidualParity
import Mathlib

/-!
# Per-base sum identity for commuting atom projections

If a finite atom map f commutes with two projections to a common base,
then regrouping its source-atom markings by f preserves the total
marking separately above *each base atom*. Global parity alone does
not suffice for the local finite-extension argument.

This statement requires no injection or surjection hypothesis on f.
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
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  have hiff (b : β) :
      (target b = a ∧ f x = b) ↔
        (source x = a ∧ f x = b) := by
    constructor
    · rintro ⟨ht, heq⟩
      refine ⟨?_, heq⟩
      calc
        source x = target (f x) := (hcomm x).symm
        _ = target b := congrArg target heq
        _ = a := ht
    · rintro ⟨hs, heq⟩
      refine ⟨?_, heq⟩
      calc
        target b = target (f x) := congrArg target heq.symm
        _ = source x := hcomm x
        _ = a := hs
  simp_rw [hiff]
  by_cases hsa : source x = a
  · simp [hsa]
  · simp [hsa]

end SuccessorTree.NonPrecompact
