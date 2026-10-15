import BANANA.NonPrecompact.PrebananaFiveAryWordStage

/-!
# The residual parity argument for finite marked-atom allocation

In the explicit pre-BANANA limit construction, choose one marked or
unmarked leaf for each target atom. The selected leaves have the same
total F₂ marking as the whole source fibre, because the target atom
markings agree over the base. The unused leaves must therefore
have marking zero, so adding them to one nonempty target bin
does not change the target bin's marking.

These algebraic lemmas isolate this final allocation step. They
do not assert that sufficiently many leaves of each mark exist,
construct the selected leaves, or prove the finite-extension theorem.
-/

namespace SuccessorTree.NonPrecompact

/-- If selected and residual atoms are disjoint and cover a finite
marked fibre, and the selected atoms have the same total parity as
the fibre, then the residual atoms have zero total parity. -/
theorem prebananaResidualMark_zero
    {ι : Type*} [DecidableEq ι] (mark : ι → F2)
    (whole selected residual : Finset ι)
    (hdisjoint : Disjoint selected residual)
    (hcover : selected ∪ residual = whole)
    (p : F2)
    (hwhole : (∑ x ∈ whole, mark x) = p)
    (hselected : (∑ x ∈ selected, mark x) = p) :
    (∑ x ∈ residual, mark x) = 0 := by
  classical
  have heq : p + (∑ x ∈ residual, mark x) = p := by
    calc
      p + (∑ x ∈ residual, mark x) =
          (∑ x ∈ selected, mark x) +
          (∑ x ∈ residual, mark x) := by rw [hselected]
      _ = ∑ x ∈ selected ∪ residual, mark x :=
        (Finset.sum_union hdisjoint).symm
      _ = ∑ x ∈ whole, mark x := by rw [hcover]
      _ = p := hwhole
  have hcancel : p + (∑ x ∈ residual, mark x) = p + 0 := by
    simpa using heq
  exact add_left_cancel hcancel

/-- Adding a disjoint collection of total parity zero to a bin
does not change the total mark of the bin. -/
theorem prebananaAddZeroMarkedResidual
    {ι : Type*} [DecidableEq ι] (mark : ι → F2)
    (bin residual : Finset ι)
    (hdisjoint : Disjoint bin residual)
    (hzero : (∑ x ∈ residual, mark x) = 0) :
    (∑ x ∈ bin ∪ residual, mark x) = ∑ x ∈ bin, mark x := by
  classical
  rw [Finset.sum_union hdisjoint, hzero, add_zero]

end SuccessorTree.NonPrecompact
