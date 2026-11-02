import BANANA.NonPrecompact.FolkmanGeneratedNonunitalRingIso
import BANANA.NonPrecompact.FolkmanTupleTermPairing

/-!
# Full pairing preservation on native generated non-unital subrings

The profile-induced maps are genuine ring isomorphisms on each sort.
Their pairing preservation follows by choosing ring-term representatives
and using the earlier all-term profile-pairing theorem. No homogeneous
limit or automorphism-extension assertion is made here.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical BigOperators

/-- Equal complete profiles give pairing-preserving native generated-ring
isomorphisms. The carriers are NonUnitalSubring closures, not unital closures
or unequipped term-value sets. Either tuple or ambient atom sort may be empty. -/
theorem folkmanGeneratedNonunitalRingEquivs_preserve_pairing
    {A B : FolkmanAtomStructure} {nL nR : ℕ}
    (xsA : Fin nL → Finset (Fin A.leftCount))
    (ysA : Fin nR → Finset (Fin A.rightCount))
    (xsB : Fin nL → Finset (Fin B.leftCount))
    (ysB : Fin nR → Finset (Fin B.rightCount))
    (h : folkmanAtomTupleProfile A xsA ysA =
      folkmanAtomTupleProfile B xsB ysB)
    (x : folkmanGeneratedNonunitalSubring (fun i => toBoolRing (xsA i)))
    (y : folkmanGeneratedNonunitalSubring (fun i => toBoolRing (ysA i))) :
    (∑ a ∈ ofBoolRing
      (folkmanGeneratedNonunitalRingEquiv_of_patterns_eq xsA xsB
        (congrArg (fun z : FolkmanAtomTupleProfile nL nR => z.1.1) h) x).val,
      ∑ b ∈ ofBoolRing
        (folkmanGeneratedNonunitalRingEquiv_of_patterns_eq ysA ysB
          (congrArg (fun z : FolkmanAtomTupleProfile nL nR => z.1.2) h) y).val,
        B.edge a b) =
      ∑ a ∈ ofBoolRing x.val, ∑ b ∈ ofBoolRing y.val, A.edge a b := by
  classical
  let hL : folkmanTupleNonzeroPatterns xsA = folkmanTupleNonzeroPatterns xsB :=
    congrArg (fun z : FolkmanAtomTupleProfile nL nR => z.1.1) h
  let hR : folkmanTupleNonzeroPatterns ysA = folkmanTupleNonzeroPatterns ysB :=
    congrArg (fun z : FolkmanAtomTupleProfile nL nR => z.1.2) h
  let t := folkmanGeneratedRingTermRepresentative
    (fun i => toBoolRing (xsA i)) x
  let u := folkmanGeneratedRingTermRepresentative
    (fun i => toBoolRing (ysA i)) y
  have ht : t.eval (fun i => toBoolRing (xsA i)) = x.val :=
    folkmanGeneratedRingTermRepresentative_spec _ x
  have hu : u.eval (fun i => toBoolRing (ysA i)) = y.val :=
    folkmanGeneratedRingTermRepresentative_spec _ y
  have hxA : ofBoolRing x.val = t.evalSet xsA := by
    rw [← ht, t.eval_toBoolRing]
    rfl
  have hyA : ofBoolRing y.val = u.evalSet ysA := by
    rw [← hu, u.eval_toBoolRing]
    rfl
  have hxB : ofBoolRing
      (folkmanGeneratedNonunitalRingEquiv_of_patterns_eq xsA xsB hL x).val =
        t.evalSet xsB := by
    have hx := folkmanGeneratedNonunitalRingEquiv_eval_term
      (fun i => toBoolRing (xsA i)) (fun i => toBoolRing (xsB i))
      (folkmanRingTerm_nativeEqualities_of_patterns_eq xsA xsB hL) x t ht
    change ofBoolRing
      (folkmanGeneratedNonunitalRingEquiv_of_termEqualities
        (fun i => toBoolRing (xsA i)) (fun i => toBoolRing (xsB i))
        (folkmanRingTerm_nativeEqualities_of_patterns_eq xsA xsB hL) x).val = _
    rw [hx, t.eval_toBoolRing]
    rfl
  have hyB : ofBoolRing
      (folkmanGeneratedNonunitalRingEquiv_of_patterns_eq ysA ysB hR y).val =
        u.evalSet ysB := by
    have hy := folkmanGeneratedNonunitalRingEquiv_eval_term
      (fun i => toBoolRing (ysA i)) (fun i => toBoolRing (ysB i))
      (folkmanRingTerm_nativeEqualities_of_patterns_eq ysA ysB hR) y u hu
    change ofBoolRing
      (folkmanGeneratedNonunitalRingEquiv_of_termEqualities
        (fun i => toBoolRing (ysA i)) (fun i => toBoolRing (ysB i))
        (folkmanRingTerm_nativeEqualities_of_patterns_eq ysA ysB hR) y).val = _
    rw [hy, u.eval_toBoolRing]
    rfl
  rw [hxA, hyA, hxB, hyB]
  have hp := folkmanNonunitalTerm_pairing_of_profile_eq
    xsA ysA xsB ysB h t.toNonunitalTerm u.toNonunitalTerm
  simpa only [FolkmanRingTerm.toNonunitalTerm_evalSet] using hp.symm

end SuccessorTree.NonPrecompact
