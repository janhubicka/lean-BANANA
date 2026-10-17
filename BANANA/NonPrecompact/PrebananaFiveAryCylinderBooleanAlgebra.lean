import BANANA.NonPrecompact.PrebananaFiveAryCylinderMark
import Mathlib.Order.BooleanSubalgebra

/-!
# Boolean-algebra structure on finite-prefix cylinders

The union, intersection and complement of cylinders are again cylinders.
For two possibly different finite levels, refine both presentations to
the same level max(n,m), using the actual marked tower maps.

The cylinder subsets form a Boolean subalgebra of the powerset of
infinite five-ary words. The previously constructed cylinder carrier
is definitionally the underlying subtype of this subalgebra, so it
inherits the standard Boolean algebra operations without recreating
the Boolean algebra laws by hand.

This is the algebraic carrier only. The marked structure and its
Fraïssé limit properties are verified in subsequent modules.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical

/-- The finite-prefix cylinders form a Boolean subalgebra of
the full Boolean algebra of infinite-word subsets. -/
noncomputable def prebananaFiveAryCylinderSubalgebra :
    BooleanSubalgebra (Set PrebananaFiveAryInfiniteWord) where
  carrier := {X | ∃ n : ℕ, ∃ s : Finset (PrebananaFiveAryWord n),
    X = prebananaFiveAryCylinder n s}
  bot_mem' := by
    exact ⟨0, ∅, (prebananaFiveAryCylinder_empty 0).symm⟩
  compl_mem' := by
    intro X hX
    obtain ⟨n, s, hs⟩ := hX
    refine ⟨n, Finset.univ \ s, ?_⟩
    rw [hs]
    exact (prebananaFiveAryCylinder_compl n s).symm
  supClosed' := by
    intro X Y hX hY
    obtain ⟨n, s, hs⟩ := hX
    obtain ⟨m, t, ht⟩ := hY
    let N := max n m
    have hn : n ≤ N := le_max_left n m
    have hm : m ≤ N := le_max_right n m
    let sn := prebananaFiveAryRefineTo n N hn s
    let tm := prebananaFiveAryRefineTo m N hm t
    refine ⟨N, sn ∪ tm, ?_⟩
    calc
      X ∪ Y = prebananaFiveAryCylinder n s ∪
        prebananaFiveAryCylinder m t := by rw [hs, ht]
      _ = prebananaFiveAryCylinder N sn ∪
        prebananaFiveAryCylinder N tm := by
          rw [prebananaFiveAryRefineTo_cylinder n N hn s,
            prebananaFiveAryRefineTo_cylinder m N hm t]
      _ = prebananaFiveAryCylinder N (sn ∪ tm) :=
        (prebananaFiveAryCylinder_union N sn tm).symm
  infClosed' := by
    intro X Y hX hY
    obtain ⟨n, s, hs⟩ := hX
    obtain ⟨m, t, ht⟩ := hY
    let N := max n m
    have hn : n ≤ N := le_max_left n m
    have hm : m ≤ N := le_max_right n m
    let sn := prebananaFiveAryRefineTo n N hn s
    let tm := prebananaFiveAryRefineTo m N hm t
    refine ⟨N, sn ∩ tm, ?_⟩
    calc
      X ∩ Y = prebananaFiveAryCylinder n s ∩
        prebananaFiveAryCylinder m t := by rw [hs, ht]
      _ = prebananaFiveAryCylinder N sn ∩
        prebananaFiveAryCylinder N tm := by
          rw [prebananaFiveAryRefineTo_cylinder n N hn s,
            prebananaFiveAryRefineTo_cylinder m N hm t]
      _ = prebananaFiveAryCylinder N (sn ∩ tm) :=
        (prebananaFiveAryCylinder_inter N sn tm).symm

/-- The existing concrete cylinder carrier inherits its Boolean
algebra structure from the standard Boolean subalgebra of sets. -/
noncomputable instance :
    BooleanAlgebra PrebananaFiveAryCylinderLimitCarrier :=
  BooleanSubalgebra.instBooleanAlgebraCoe
    prebananaFiveAryCylinderSubalgebra

@[simp] theorem prebananaFiveAryCylinder_val_bot :
    ((⊥ : PrebananaFiveAryCylinderLimitCarrier).val :
      Set PrebananaFiveAryInfiniteWord) = ∅ := rfl

@[simp] theorem prebananaFiveAryCylinder_val_top :
    ((⊤ : PrebananaFiveAryCylinderLimitCarrier).val :
      Set PrebananaFiveAryInfiniteWord) = Set.univ := rfl

@[simp] theorem prebananaFiveAryCylinder_val_sup
    (X Y : PrebananaFiveAryCylinderLimitCarrier) :
    (X ⊔ Y).val = X.val ∪ Y.val := rfl

@[simp] theorem prebananaFiveAryCylinder_val_inf
    (X Y : PrebananaFiveAryCylinderLimitCarrier) :
    (X ⊓ Y).val = X.val ∩ Y.val := rfl

@[simp] theorem prebananaFiveAryCylinder_val_compl
    (X : PrebananaFiveAryCylinderLimitCarrier) :
    Xᶜ.val = X.valᶜ := rfl

end SuccessorTree.NonPrecompact
