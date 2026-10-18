import BANANA.NonPrecompact.PrebananaFiveAryCylinderLimitCarrier

/-!
# The explicit countable pre-BANANA cylinder algebra is infinite

The cylinder carrier is already proved countable. To show it is
infinite, use the cylinder given by fixing coordinate n of an
infinite five-ary branch to the value 1. Distinct coordinates
define distinct subsets, witnessed by a branch which takes value
1 at just one chosen coordinate and 0 elsewhere.

This gives a concrete injection of ℕ into the cylinder carrier
without cardinal-arithmetic estimates for finite tower stages.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical

/-- The cylinder fixing the nth coordinate to 1, presented at
the finite word depth n+1. -/
noncomputable def prebananaFiveAryCoordinateCylinder (n : ℕ) :
    PrebananaFiveAryCylinderLimitCarrier :=
  let s : Finset (PrebananaFiveAryWord (n + 1)) :=
    Finset.univ.filter
      (fun w => w ⟨n, Nat.lt_succ_self n⟩ = (1 : Fin 5))
  ⟨prebananaFiveAryCylinder (n + 1) s, ⟨n + 1, s, rfl⟩⟩

/-- Membership in the coordinate cylinder has its literal
meaning on infinite branches. -/
theorem prebananaFiveAryCoordinateCylinder_mem_iff
    (n : ℕ) (w : PrebananaFiveAryInfiniteWord) :
    w ∈ (prebananaFiveAryCoordinateCylinder n).val ↔
      w n = (1 : Fin 5) := by
  simp [prebananaFiveAryCoordinateCylinder, prebananaFiveAryCylinder,
    prebananaFiveAryInfinitePrefix]

/-- Different natural-number coordinates yield different
cylinder elements. -/
theorem prebananaFiveAryCoordinateCylinder_injective :
    Function.Injective prebananaFiveAryCoordinateCylinder := by
  intro n m hnm
  let w : PrebananaFiveAryInfiniteWord :=
    fun i => if i = n then 1 else 0
  have hn : w ∈ (prebananaFiveAryCoordinateCylinder n).val := by
    apply (prebananaFiveAryCoordinateCylinder_mem_iff n w).mpr
    simp [w]
  have hm : w ∈ (prebananaFiveAryCoordinateCylinder m).val := by
    rw [← congrArg Subtype.val hnm]
    exact hn
  have hm1 : w m = (1 : Fin 5) :=
    (prebananaFiveAryCoordinateCylinder_mem_iff m w).mp hm
  have hmn : m = n := by
    by_contra h
    have hm0 : w m = (0 : Fin 5) := by
      simp [w, h]
    have h01 : (0 : Fin 5) = 1 := hm0.symm.trans hm1
    exact (by decide : (0 : Fin 5) ≠ 1) h01
  exact hmn.symm

/-- In addition to being countable, the actual pre-BANANA
cylinder carrier is infinite. -/
noncomputable instance : Infinite PrebananaFiveAryCylinderLimitCarrier :=
  Infinite.of_injective prebananaFiveAryCoordinateCylinder
    prebananaFiveAryCoordinateCylinder_injective

end SuccessorTree.NonPrecompact
