import BANANA.NonPrecompact.FolkmanTupleProfilesPairingTransport
import BANANA.NonPrecompact.PrebananaBooleanTerms

/-!
# Term equalities for non-unital Folkman tuple profiles

The ambient finite Boolean ring is a powerset ring, with addition given
by symmetric difference and multiplication by intersection. Its
finitely generated non-unital part consists of term values with no
constant contribution outside the supports of the generators.

We reuse the Boolean-term syntax and evaluation lemmas from pre-BANANA,
but *restrict terms by their value on the all-zero atom signature*.
This condition avoids incorrectly adjoining the ambient unit.

Equal sets of realised nonzero signatures determine all equations
between these terms. Consequently they give a canonical equivalence of
the non-unital term-value ranges, mapping every distinguished generator
to its counterpart.

This file does not yet identify term-value ranges with native generated
subrings, prove preservation of the cross-sort pairing on all term
values, or extend the equivalence to an automorphism of a limit.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical

/-- A Boolean term without an ambient constant-one contribution.
Such a term evaluates to zero on every atom outside the union of the
distinguished generators. This definition includes empty tuples. -/
abbrev FolkmanNonunitalTerm (n : ℕ) :=
  {t : PrebananaBooleanTerm n //
    t.evalPattern (folkmanZeroTuplePattern n) = false}

/-- The zero term is non-unital. -/
def FolkmanNonunitalTerm.zero (n : ℕ) : FolkmanNonunitalTerm n :=
  ⟨.zero, rfl⟩

/-- A named generator is a non-unital term. -/
def FolkmanNonunitalTerm.generator {n : ℕ} (i : Fin n) :
    FolkmanNonunitalTerm n :=
  ⟨.generator i, rfl⟩

/-- Reuse the generic pre-BANANA term interpretation on Folkman atoms.
No pre-BANANA mark or positivity hypothesis is involved. -/
theorem PrebananaBooleanTerm.mem_evalSet_iff_folkmanSignature
    {n atoms : ℕ}
    (xs : Fin n → Finset (Fin atoms))
    (a : Fin atoms) (t : PrebananaBooleanTerm n) :
    a ∈ t.evalSet xs ↔
      t.evalPattern (folkmanAtomTupleSignature xs a) = true := by
  classical
  induction t with
  | zero =>
      simp [evalSet, evalPattern]
  | one =>
      simp [evalSet, evalPattern]
  | generator i =>
      simpa [evalSet, evalPattern] using
        (folkmanAtomTupleSignature_true_iff xs a i).symm
  | complement t ih =>
      simp [evalSet, evalPattern, ih]
  | join t u iht ihu =>
      simp [evalSet, evalPattern, iht, ihu]
  | meet t u iht ihu =>
      simp [evalSet, evalPattern, iht, ihu]

/-- For terms vanishing on the all-zero pattern, equality of
evaluations is determined exactly by the realised *nonzero* patterns.
This remains true when the atom set or the tuple is empty. -/
theorem folkmanBooleanTerm_evalSet_eq_iff_nonzeroPatterns
    {n atoms : ℕ}
    (xs : Fin n → Finset (Fin atoms))
    (t u : PrebananaBooleanTerm n)
    (ht : t.evalPattern (folkmanZeroTuplePattern n) = false)
    (hu : u.evalPattern (folkmanZeroTuplePattern n) = false) :
    t.evalSet xs = u.evalSet xs ↔
      ∀ p ∈ folkmanTupleNonzeroPatterns xs,
        t.evalPattern p = u.evalPattern p := by
  classical
  constructor
  · intro heq p hp
    change p ∈
      ((Finset.univ : Finset (Fin atoms)).image
        (folkmanAtomTupleSignature xs)).filter
          (fun q => q ≠ folkmanZeroTuplePattern n) at hp
    obtain ⟨a, _, hpa⟩ :=
      Finset.mem_image.mp (Finset.mem_filter.mp hp).1
    have hmem : a ∈ t.evalSet xs ↔ a ∈ u.evalSet xs := by
      rw [heq]
    rw [t.mem_evalSet_iff_folkmanSignature xs a,
      u.mem_evalSet_iff_folkmanSignature xs a, hpa] at hmem
    cases ht' : t.evalPattern p <;>
      cases hu' : u.evalPattern p <;> simp_all
  · intro hpattern
    apply Finset.ext
    intro a
    rw [t.mem_evalSet_iff_folkmanSignature xs a,
      u.mem_evalSet_iff_folkmanSignature xs a]
    by_cases hz :
        folkmanAtomTupleSignature xs a = folkmanZeroTuplePattern n
    · simp [hz, ht, hu]
    · have hp :
          folkmanAtomTupleSignature xs a ∈
            folkmanTupleNonzeroPatterns xs := by
        change folkmanAtomTupleSignature xs a ∈
          ((Finset.univ : Finset (Fin atoms)).image
            (folkmanAtomTupleSignature xs)).filter
              (fun q => q ≠ folkmanZeroTuplePattern n)
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩, hz⟩
      rw [hpattern _ hp]

/-- Equal nonzero pattern sets give the same equations between
non-unital terms, without reference to a pairing or a limit. -/
theorem folkmanNonunitalTerm_equalities_of_patterns_eq
    {n atomsA atomsB : ℕ}
    (xsA : Fin n → Finset (Fin atomsA))
    (xsB : Fin n → Finset (Fin atomsB))
    (hpatterns : folkmanTupleNonzeroPatterns xsA =
      folkmanTupleNonzeroPatterns xsB)
    (t u : FolkmanNonunitalTerm n) :
    (t.val.evalSet xsA = u.val.evalSet xsA) ↔
      (t.val.evalSet xsB = u.val.evalSet xsB) := by
  calc
    (t.val.evalSet xsA = u.val.evalSet xsA) ↔
        (∀ p ∈ folkmanTupleNonzeroPatterns xsA,
          t.val.evalPattern p = u.val.evalPattern p) :=
      folkmanBooleanTerm_evalSet_eq_iff_nonzeroPatterns
        xsA t.val u.val t.property u.property
    _ ↔ (∀ p ∈ folkmanTupleNonzeroPatterns xsB,
          t.val.evalPattern p = u.val.evalPattern p) := by
      rw [hpatterns]
    _ ↔ (t.val.evalSet xsB = u.val.evalSet xsB) :=
      (folkmanBooleanTerm_evalSet_eq_iff_nonzeroPatterns
        xsB t.val u.val t.property u.property).symm

/-- Values of all non-unital terms in one tuple. It is important
that this is not the unital BooleanSubalgebra of the ambient ring. -/
def folkmanNonunitalTermRange
    {n atoms : ℕ} (xs : Fin n → Finset (Fin atoms)) : Type :=
  {s : Finset (Fin atoms) //
    ∃ t : FolkmanNonunitalTerm n, t.val.evalSet xs = s}

/-- Canonical equivalence of non-unital term values under equality
of realised nonzero membership patterns. -/
noncomputable def folkmanNonunitalTermRangeEquiv_of_patterns_eq
    {n atomsA atomsB : ℕ}
    (xsA : Fin n → Finset (Fin atomsA))
    (xsB : Fin n → Finset (Fin atomsB))
    (hpatterns : folkmanTupleNonzeroPatterns xsA =
      folkmanTupleNonzeroPatterns xsB) :
    folkmanNonunitalTermRange xsA ≃
      folkmanNonunitalTermRange xsB := by
  classical
  let hEq : ∀ t u : FolkmanNonunitalTerm n,
      (t.val.evalSet xsA = u.val.evalSet xsA) ↔
        (t.val.evalSet xsB = u.val.evalSet xsB) :=
    folkmanNonunitalTerm_equalities_of_patterns_eq xsA xsB hpatterns
  let toB (x : folkmanNonunitalTermRange xsA) :
      folkmanNonunitalTermRange xsB :=
    ⟨(Classical.choose x.property).val.evalSet xsB,
      ⟨Classical.choose x.property, rfl⟩⟩
  let toA (y : folkmanNonunitalTermRange xsB) :
      folkmanNonunitalTermRange xsA :=
    ⟨(Classical.choose y.property).val.evalSet xsA,
      ⟨Classical.choose y.property, rfl⟩⟩
  refine {
    toFun := toB
    invFun := toA
    left_inv := ?_
    right_inv := ?_
  }
  · intro x
    apply Subtype.ext
    change (Classical.choose (toB x).property).val.evalSet xsA = x.val
    have hB :
        (Classical.choose (toB x).property).val.evalSet xsB =
          (Classical.choose x.property).val.evalSet xsB :=
      Classical.choose_spec (toB x).property
    exact ((hEq _ _).mpr hB).trans (Classical.choose_spec x.property)
  · intro y
    apply Subtype.ext
    change (Classical.choose (toA y).property).val.evalSet xsB = y.val
    have hA :
        (Classical.choose (toA y).property).val.evalSet xsA =
          (Classical.choose y.property).val.evalSet xsA :=
      Classical.choose_spec (toA y).property
    exact ((hEq _ _).mp hA).trans (Classical.choose_spec y.property)

/-- The equivalence sends each evaluated non-unital term to the
evaluation of the *same* term in the second tuple. -/
theorem folkmanNonunitalTermRangeEquiv_eval_term
    {n atomsA atomsB : ℕ}
    (xsA : Fin n → Finset (Fin atomsA))
    (xsB : Fin n → Finset (Fin atomsB))
    (hpatterns : folkmanTupleNonzeroPatterns xsA =
      folkmanTupleNonzeroPatterns xsB)
    (t : FolkmanNonunitalTerm n) :
    ((folkmanNonunitalTermRangeEquiv_of_patterns_eq
        xsA xsB hpatterns)
      ⟨t.val.evalSet xsA, ⟨t, rfl⟩⟩).val =
        t.val.evalSet xsB := by
  classical
  let x : folkmanNonunitalTermRange xsA :=
    ⟨t.val.evalSet xsA, ⟨t, rfl⟩⟩
  have hx :
      (Classical.choose x.property).val.evalSet xsA =
        t.val.evalSet xsA := Classical.choose_spec x.property
  change (Classical.choose x.property).val.evalSet xsB =
    t.val.evalSet xsB
  exact (folkmanNonunitalTerm_equalities_of_patterns_eq
    xsA xsB hpatterns _ t).mp hx

/-- The left-side generator-preserving term equivalence supplied
by equality of complete two-sort Folkman profiles. -/
noncomputable def folkmanLeftTermRangeEquiv_of_profile_eq
    {A B : FolkmanAtomStructure}
    {nL nR : ℕ}
    (xsA : Fin nL → Finset (Fin A.leftCount))
    (ysA : Fin nR → Finset (Fin A.rightCount))
    (xsB : Fin nL → Finset (Fin B.leftCount))
    (ysB : Fin nR → Finset (Fin B.rightCount))
    (h : folkmanAtomTupleProfile A xsA ysA =
      folkmanAtomTupleProfile B xsB ysB) :
    folkmanNonunitalTermRange xsA ≃
      folkmanNonunitalTermRange xsB :=
  folkmanNonunitalTermRangeEquiv_of_patterns_eq xsA xsB
    (congrArg (fun z : FolkmanAtomTupleProfile nL nR => z.1.1) h)

/-- The corresponding right-side equivalence, using the same
generic theorem rather than a second copy of the proof. -/
noncomputable def folkmanRightTermRangeEquiv_of_profile_eq
    {A B : FolkmanAtomStructure}
    {nL nR : ℕ}
    (xsA : Fin nL → Finset (Fin A.leftCount))
    (ysA : Fin nR → Finset (Fin A.rightCount))
    (xsB : Fin nL → Finset (Fin B.leftCount))
    (ysB : Fin nR → Finset (Fin B.rightCount))
    (h : folkmanAtomTupleProfile A xsA ysA =
      folkmanAtomTupleProfile B xsB ysB) :
    folkmanNonunitalTermRange ysA ≃
      folkmanNonunitalTermRange ysB :=
  folkmanNonunitalTermRangeEquiv_of_patterns_eq ysA ysB
    (congrArg (fun z : FolkmanAtomTupleProfile nL nR => z.1.2) h)

end SuccessorTree.NonPrecompact
