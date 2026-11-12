import BANANA.NonPrecompact.FolkmanTupleTermPairing

/-!
# Pair-preserving equivalences of finite Folkman term-value structures

Equality of complete two-sort tuple profiles gives equivalences of
the left and right non-unital term-value ranges. This file combines
the common-term interpretation theorem and the finite pairing-sum
formula to show that these equivalences preserve the bilinear map
on *all* generated term values.

It does not silently replace the two term-value ranges by native
Boolean subrings: that interface and the homogeneous-limit extension
theorem must be validated separately.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical BigOperators

/-- The canonical pair of term-value equivalences obtained from
equal complete Folkman profiles preserves the cross-sort pairing on
every pair of term values. This includes empty tuples and zero rings. -/
theorem folkmanTermRangeEquivs_preserve_pairing_of_profile_eq
    {A B : FolkmanAtomStructure}
    {nL nR : ℕ}
    (xsA : Fin nL → Finset (Fin A.leftCount))
    (ysA : Fin nR → Finset (Fin A.rightCount))
    (xsB : Fin nL → Finset (Fin B.leftCount))
    (ysB : Fin nR → Finset (Fin B.rightCount))
    (h : folkmanAtomTupleProfile A xsA ysA =
      folkmanAtomTupleProfile B xsB ysB)
    (x : folkmanNonunitalTermRange xsA)
    (y : folkmanNonunitalTermRange ysA) :
    (∑ a ∈
      (folkmanLeftTermRangeEquiv_of_profile_eq xsA ysA xsB ysB h x).val,
      ∑ b ∈
        (folkmanRightTermRangeEquiv_of_profile_eq xsA ysA xsB ysB h y).val,
          B.edge a b) =
    (∑ a ∈ x.val, ∑ b ∈ y.val, A.edge a b) := by
  classical
  let t : FolkmanNonunitalTerm nL := Classical.choose x.property
  let u : FolkmanNonunitalTerm nR := Classical.choose y.property
  have hxA : t.val.evalSet xsA = x.val :=
    Classical.choose_spec x.property
  have hyA : u.val.evalSet ysA = y.val :=
    Classical.choose_spec y.property
  have hleft : folkmanTupleNonzeroPatterns xsA =
      folkmanTupleNonzeroPatterns xsB :=
    congrArg (fun z : FolkmanAtomTupleProfile nL nR => z.1.1) h
  have hright : folkmanTupleNonzeroPatterns ysA =
      folkmanTupleNonzeroPatterns ysB :=
    congrArg (fun z : FolkmanAtomTupleProfile nL nR => z.1.2) h
  have hxB :
      (folkmanLeftTermRangeEquiv_of_profile_eq
        xsA ysA xsB ysB h x).val = t.val.evalSet xsB := by
    have hx : x =
        (⟨t.val.evalSet xsA, ⟨t, rfl⟩⟩ :
          folkmanNonunitalTermRange xsA) := by
      apply Subtype.ext
      exact hxA.symm
    rw [hx]
    exact folkmanNonunitalTermRangeEquiv_eval_term
      xsA xsB hleft t
  have hyB :
      (folkmanRightTermRangeEquiv_of_profile_eq
        xsA ysA xsB ysB h y).val = u.val.evalSet ysB := by
    have hy : y =
        (⟨u.val.evalSet ysA, ⟨u, rfl⟩⟩ :
          folkmanNonunitalTermRange ysA) := by
      apply Subtype.ext
      exact hyA.symm
    rw [hy]
    exact folkmanNonunitalTermRangeEquiv_eval_term
      ysA ysB hright u
  calc
    (∑ a ∈
      (folkmanLeftTermRangeEquiv_of_profile_eq xsA ysA xsB ysB h x).val,
      ∑ b ∈
        (folkmanRightTermRangeEquiv_of_profile_eq xsA ysA xsB ysB h y).val,
          B.edge a b) =
        (∑ a ∈ t.val.evalSet xsB,
          ∑ b ∈ u.val.evalSet ysB, B.edge a b) := by
      rw [hxB, hyB]
    _ = (∑ a ∈ t.val.evalSet xsA,
          ∑ b ∈ u.val.evalSet ysA, A.edge a b) :=
      (folkmanNonunitalTerm_pairing_of_profile_eq
        xsA ysA xsB ysB h t u).symm
    _ = (∑ a ∈ x.val, ∑ b ∈ y.val, A.edge a b) := by
      rw [hxA, hyA]

end SuccessorTree.NonPrecompact
