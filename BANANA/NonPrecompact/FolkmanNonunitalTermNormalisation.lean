import BANANA.NonPrecompact.FolkmanNonunitalRingTerms

/-!
# Eliminating the ambient unit from zero-preserving Boolean terms

For every Boolean term t we construct a genuine non-unital ring term
whose truth function is t(p) xor t(0). A term vanishing at the zero
signature therefore has exactly the same values as this ring term.
This identifies the earlier restricted Boolean-term range with the
native generated non-unital subring, including empty tuples.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical symmDiff

/-- The nonconstant part of (r+c)(s+d), where c and d are Boolean constants. -/
def folkmanCentredProduct {n : ℕ} (c d : Bool)
    (r s : FolkmanRingTerm n) : FolkmanRingTerm n :=
  .add (.add (.mul r s) (if c then s else .zero))
    (if d then r else .zero)

/-- Remove the value at the zero signature without introducing a unit. -/
def PrebananaBooleanTerm.centredRingTerm {n : ℕ} :
    PrebananaBooleanTerm n → FolkmanRingTerm n
  | .zero => .zero
  | .one => .zero
  | .generator i => .generator i
  | .complement t => t.centredRingTerm
  | .meet t u => folkmanCentredProduct
      (t.evalPattern (folkmanZeroTuplePattern n))
      (u.evalPattern (folkmanZeroTuplePattern n))
      t.centredRingTerm u.centredRingTerm
  | .join t u => .add (.add t.centredRingTerm u.centredRingTerm)
      (folkmanCentredProduct
        (t.evalPattern (folkmanZeroTuplePattern n))
        (u.evalPattern (folkmanZeroTuplePattern n))
        t.centredRingTerm u.centredRingTerm)

/-- The compiler invariant, including terms that do not vanish at zero. -/
theorem PrebananaBooleanTerm.centredRingTerm_evalPattern
    {n : ℕ} (t : PrebananaBooleanTerm n) (p : Fin n → Bool) :
    t.centredRingTerm.evalPattern p =
      Bool.xor (t.evalPattern p)
        (t.evalPattern (folkmanZeroTuplePattern n)) := by
  induction t with
  | zero => rfl
  | one => rfl
  | generator i =>
      cases hp : p i <;>
        simp [centredRingTerm, FolkmanRingTerm.evalPattern,
          evalPattern, folkmanZeroTuplePattern, hp]
  | complement t ih =>
      cases hp : t.evalPattern p <;>
        cases hz : t.evalPattern (folkmanZeroTuplePattern n) <;>
        simp [centredRingTerm, evalPattern, ih, hp, hz]
  | meet t u iht ihu =>
      cases ht : t.evalPattern p <;>
        cases hu : u.evalPattern p <;>
        cases hzt : t.evalPattern (folkmanZeroTuplePattern n) <;>
        cases hzu : u.evalPattern (folkmanZeroTuplePattern n) <;>
        simp [centredRingTerm, folkmanCentredProduct,
          FolkmanRingTerm.evalPattern, evalPattern, iht, ihu, ht, hu, hzt, hzu]
  | join t u iht ihu =>
      cases ht : t.evalPattern p <;>
        cases hu : u.evalPattern p <;>
        cases hzt : t.evalPattern (folkmanZeroTuplePattern n) <;>
        cases hzu : u.evalPattern (folkmanZeroTuplePattern n) <;>
        simp [centredRingTerm, folkmanCentredProduct,
          FolkmanRingTerm.evalPattern, evalPattern, iht, ihu, ht, hu, hzt, hzu]

/-- Interpret ring syntax as the previously used Boolean syntax. -/
def FolkmanRingTerm.toBooleanTerm {n : ℕ} :
    FolkmanRingTerm n → PrebananaBooleanTerm n
  | .zero => .zero
  | .generator i => .generator i
  | .add t u => .join
      (.meet t.toBooleanTerm (.complement u.toBooleanTerm))
      (.meet (.complement t.toBooleanTerm) u.toBooleanTerm)
  | .mul t u => .meet t.toBooleanTerm u.toBooleanTerm

theorem FolkmanRingTerm.toBooleanTerm_evalPattern
    {n : ℕ} (t : FolkmanRingTerm n) (p : Fin n → Bool) :
    t.toBooleanTerm.evalPattern p = t.evalPattern p := by
  induction t with
  | zero => rfl
  | generator i => rfl
  | add t u iht ihu =>
      cases ht : t.evalPattern p <;> cases hu : u.evalPattern p <;>
        simp [toBooleanTerm, PrebananaBooleanTerm.evalPattern,
          evalPattern, iht, ihu, ht, hu]
  | mul t u iht ihu =>
      simp [toBooleanTerm, PrebananaBooleanTerm.evalPattern,
        evalPattern, iht, ihu]

def FolkmanRingTerm.toNonunitalTerm
    {n : ℕ} (t : FolkmanRingTerm n) : FolkmanNonunitalTerm n :=
  ⟨t.toBooleanTerm, by
    rw [t.toBooleanTerm_evalPattern, t.evalPattern_zero]⟩

theorem FolkmanRingTerm.toNonunitalTerm_evalSet
    {n atoms : ℕ} (xs : Fin n → Finset (Fin atoms))
    (t : FolkmanRingTerm n) :
    t.toNonunitalTerm.val.evalSet xs = t.evalSet xs := by
  ext a
  rw [PrebananaBooleanTerm.mem_evalSet_iff_folkmanSignature,
    FolkmanRingTerm.mem_evalSet_iff]
  change t.toBooleanTerm.evalPattern (folkmanAtomTupleSignature xs a) = true ↔
    t.evalPattern (folkmanAtomTupleSignature xs a) = true
  rw [t.toBooleanTerm_evalPattern]

/-- Every restricted Boolean term has a genuine ring-term representative. -/
theorem FolkmanNonunitalTerm.centredRingTerm_evalSet
    {n atoms : ℕ} (xs : Fin n → Finset (Fin atoms))
    (t : FolkmanNonunitalTerm n) :
    t.val.centredRingTerm.evalSet xs = t.val.evalSet xs := by
  ext a
  rw [FolkmanRingTerm.mem_evalSet_iff,
    PrebananaBooleanTerm.mem_evalSet_iff_folkmanSignature,
    PrebananaBooleanTerm.centredRingTerm_evalPattern, t.property]
  cases hp : t.val.evalPattern (folkmanAtomTupleSignature xs a) <;> simp

/-- Equality of the two syntactic descriptions of generated elements. -/
theorem folkmanNonunitalTermRange_iff_ringTerm
    {n atoms : ℕ} (xs : Fin n → Finset (Fin atoms))
    (x : Finset (Fin atoms)) :
    (∃ t : FolkmanNonunitalTerm n, t.val.evalSet xs = x) ↔
      ∃ t : FolkmanRingTerm n, t.evalSet xs = x := by
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t.val.centredRingTerm, (t.centredRingTerm_evalSet xs).trans ht⟩
  · rintro ⟨t, ht⟩
    exact ⟨t.toNonunitalTerm, (t.toNonunitalTerm_evalSet xs).trans ht⟩

/-- The earlier term range is precisely the native non-unital closure,
not the ambient unital Boolean subalgebra. -/
theorem folkmanNonunitalTermRange_iff_nativeClosure
    {n atoms : ℕ} (xs : Fin n → Finset (Fin atoms))
    (x : Finset (Fin atoms)) :
    (∃ t : FolkmanNonunitalTerm n, t.val.evalSet xs = x) ↔
      toBoolRing x ∈ folkmanGeneratedNonunitalSubring
        (fun i => toBoolRing (xs i)) := by
  rw [folkmanNonunitalTermRange_iff_ringTerm,
    folkmanGeneratedNonunitalSubring_mem_iff_ringTerm]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, (t.eval_toBoolRing xs).trans (congrArg toBoolRing ht)⟩
  · rintro ⟨t, ht⟩
    refine ⟨t, toBoolRing.injective ?_⟩
    exact (t.eval_toBoolRing xs).symm.trans ht

/-- Carrier identification with Mathlib's actual generated non-unital subring. -/
noncomputable def folkmanNonunitalTermRangeEquivGenerated
    {n atoms : ℕ} (xs : Fin n → Finset (Fin atoms)) :
    folkmanNonunitalTermRange xs ≃
      folkmanGeneratedNonunitalSubring (fun i => toBoolRing (xs i)) where
  toFun x := ⟨toBoolRing x.val,
    (folkmanNonunitalTermRange_iff_nativeClosure xs x.val).mp x.property⟩
  invFun y := ⟨ofBoolRing y.val,
    (folkmanNonunitalTermRange_iff_nativeClosure xs (ofBoolRing y.val)).mpr
      (by simpa only [toBoolRing_ofBoolRing] using y.property)⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv y := by apply Subtype.ext; rfl

end SuccessorTree.NonPrecompact
