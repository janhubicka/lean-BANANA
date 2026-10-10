import BANANA.NonPrecompact.FiberProductParityAmalgam

/-!
# Total parity of the pre-BANANA fibre-grid marking

The row-parity formula for the star-marked compatible atom grid
also determines its total marking: summing all marked grid
atoms gives precisely the sum of marks of B. Thus, if B has
even total marking, so does the amalgam.

The result is independent of the source-coordinate presentation.
It is a key step in constructing an actual finite pre-BANANA
structure on the compatible atom grid.
-/

namespace SuccessorTree.NonPrecompact

open scoped BigOperators

/-- A sum over the compatible grid can be taken fibre by fibre.
The total mark agrees with the sum of the B-atom marks; no
compatibility condition with the C-marks is needed for this
particular equality, since the row identities always hold. -/
theorem sum_fiberGridMark_eq_sum_left
    {A B C : Type*}
    [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (f : B → A) (g : C → A)
    (hf : Function.Surjective f)
    (hg : Function.Surjective g)
    (markB : B → F2) (markC : C → F2) :
    (∑ p : FiberGrid f g,
      fiberGridMark f g hf hg markB markC p) =
    ∑ b : B, markB b := by
  classical
  calc
    (∑ p : FiberGrid f g,
      fiberGridMark f g hf hg markB markC p) =
        ∑ a : A, ∑ b : LeftFiber f a,
          ∑ c : RightFiber g a,
            fiberGridMark f g hf hg markB markC
              ⟨a, (b, c)⟩ := by
          simp only [FiberGrid, Fintype.sum_sigma,
            Fintype.sum_prod_type]
    _ = ∑ a : A, ∑ b : LeftFiber f a, markB b.1 := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      obtain ⟨bb, hbb⟩ := b
      subst a
      simpa using
        (sum_fiberGridMark_right f g hf hg markB markC bb)
    _ = ∑ b : B, markB b := by
      simpa using (Fintype.sum_fiberwise f markB)

/-- Every fibre-product star marking has even total parity as
soon as the old B marking has even total parity. -/
theorem fiberGridMark_total_zero
    {A B C : Type*}
    [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (f : B → A) (g : C → A)
    (hf : Function.Surjective f)
    (hg : Function.Surjective g)
    (markB : B → F2) (markC : C → F2)
    (hB : (∑ b : B, markB b) = 0) :
    (∑ p : FiberGrid f g,
      fiberGridMark f g hf hg markB markC p) = 0 := by
  rw [sum_fiberGridMark_eq_sum_left f g hf hg markB markC]
  exact hB

end SuccessorTree.NonPrecompact
