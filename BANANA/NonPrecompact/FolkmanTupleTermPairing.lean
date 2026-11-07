import BANANA.NonPrecompact.FolkmanTupleTermEquations

/-!
# Pairing of non-unital Folkman term values from complete tuple profiles

The pairing of two term values is the sum of the matrix entries between
the nonzero membership-pattern fibres selected by those terms.

The same finite sum/disjoint-fibre argument works on both sorts. It
avoids assuming that an ambient atom outside the generated non-unital
ring belongs to the subring. Equal complete profiles therefore give
the same pairing for *every* pair of non-unital term evaluations.

This module concerns finite atom models. The native generated-subring
identification and homogeneous countable limit are separate tasks.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical BigOperators

/-- Patterns on which a Boolean term has truth value one. -/
noncomputable def folkmanBooleanTermSelectedPatterns
    {n : ℕ} (t : PrebananaBooleanTerm n) :
    Finset (Fin n → Bool) :=
  (Finset.univ : Finset (Fin n → Bool)).filter
    (fun p => t.evalPattern p = true)

/-- Evaluating a Boolean term selects the union of the ambient
pattern fibres on which the term is true. This statement is valid
for both unital and non-unital terms. -/
theorem folkmanBooleanTerm_evalSet_eq_selectedPatternUnion
    {n atoms : ℕ}
    (xs : Fin n → Finset (Fin atoms))
    (t : PrebananaBooleanTerm n) :
    t.evalSet xs =
      (folkmanBooleanTermSelectedPatterns t).biUnion
        (folkmanTuplePatternFiber xs) := by
  classical
  ext a
  constructor
  · intro ha
    let p := folkmanAtomTupleSignature xs a
    have hp : t.evalPattern p = true :=
      (t.mem_evalSet_iff_folkmanSignature xs a).mp ha
    apply Finset.mem_biUnion.mpr
    refine ⟨p, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  · intro ha
    obtain ⟨p, hp, hfib⟩ := Finset.mem_biUnion.mp ha
    have hptrue : t.evalPattern p = true :=
      (Finset.mem_filter.mp hp).2
    have hsig : folkmanAtomTupleSignature xs a = p :=
      (Finset.mem_filter.mp hfib).2
    exact (t.mem_evalSet_iff_folkmanSignature xs a).mpr (by
      rw [hsig]
      exact hptrue)

/-- Distinct atom-membership signatures have disjoint fibres.
This is the same owner-fibre principle already used for Folkman
embeddings, now indexed by arbitrary signature functions. -/
theorem folkmanTuplePatternFiber_pairwiseDisjoint
    {n atoms : ℕ}
    (xs : Fin n → Finset (Fin atoms))
    (labels : Finset (Fin n → Bool)) :
    (labels : Set (Fin n → Bool)).PairwiseDisjoint
      (folkmanTuplePatternFiber xs) := by
  intro p hp q hq hpq
  change Disjoint (folkmanTuplePatternFiber xs p)
    (folkmanTuplePatternFiber xs q)
  rw [Finset.disjoint_left]
  intro a hap haq
  have hp' : folkmanAtomTupleSignature xs a = p :=
    (Finset.mem_filter.mp hap).2
  have hq' : folkmanAtomTupleSignature xs a = q :=
    (Finset.mem_filter.mp haq).2
  exact hpq (hp'.symm.trans hq')

/-- A non-unital term never selects the all-zero atom signature. -/
theorem folkmanNonunitalTerm_zero_not_selected
    {n : ℕ} (t : FolkmanNonunitalTerm n) :
    folkmanZeroTuplePattern n ∉
      folkmanBooleanTermSelectedPatterns t.val := by
  classical
  simp [folkmanBooleanTermSelectedPatterns, t.property]

/-- The pairing on unions of selected *nonzero* pattern fibres is
the sum of the corresponding finite profile matrix entries.
This requires no surjectivity or embedding assumptions. -/
theorem folkmanTuplePatternPairing_biUnion
    (A : FolkmanAtomStructure)
    {nL nR : ℕ}
    (xs : Fin nL → Finset (Fin A.leftCount))
    (ys : Fin nR → Finset (Fin A.rightCount))
    (L : Finset (Fin nL → Bool))
    (R : Finset (Fin nR → Bool))
    (hL : folkmanZeroTuplePattern nL ∉ L)
    (hR : folkmanZeroTuplePattern nR ∉ R) :
    (∑ a ∈ L.biUnion (folkmanTuplePatternFiber xs),
      ∑ b ∈ R.biUnion (folkmanTuplePatternFiber ys),
        A.edge a b) =
      ∑ p ∈ L, ∑ q ∈ R,
        folkmanTuplePatternPairing A xs ys p q := by
  classical
  rw [Finset.sum_biUnion
    (folkmanTuplePatternFiber_pairwiseDisjoint xs L)]
  apply Finset.sum_congr rfl
  intro p hp
  calc
    (∑ a ∈ folkmanTuplePatternFiber xs p,
      ∑ b ∈ R.biUnion (folkmanTuplePatternFiber ys),
        A.edge a b) =
      ∑ a ∈ folkmanTuplePatternFiber xs p,
        ∑ q ∈ R, ∑ b ∈ folkmanTuplePatternFiber ys q,
          A.edge a b := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.sum_biUnion
          (folkmanTuplePatternFiber_pairwiseDisjoint ys R)]
    _ = ∑ q ∈ R,
          ∑ a ∈ folkmanTuplePatternFiber xs p,
            ∑ b ∈ folkmanTuplePatternFiber ys q,
              A.edge a b := by
        rw [Finset.sum_comm]
    _ = ∑ q ∈ R, folkmanTuplePatternPairing A xs ys p q := by
        apply Finset.sum_congr rfl
        intro q hq
        have hpne : p ≠ folkmanZeroTuplePattern nL := by
          intro hzero
          apply hL
          simpa [hzero] using hp
        have hqne : q ≠ folkmanZeroTuplePattern nR := by
          intro hzero
          apply hR
          simpa [hzero] using hq
        simp [folkmanTuplePatternPairing, hpne, hqne]

/-- All cross-sort pairings of non-unital term values can be read
from the finite tuple profile alone. -/
theorem folkmanNonunitalTerm_pairing_eq_profile_sum
    (A : FolkmanAtomStructure)
    {nL nR : ℕ}
    (xs : Fin nL → Finset (Fin A.leftCount))
    (ys : Fin nR → Finset (Fin A.rightCount))
    (t : FolkmanNonunitalTerm nL)
    (u : FolkmanNonunitalTerm nR) :
    (∑ a ∈ t.val.evalSet xs,
      ∑ b ∈ u.val.evalSet ys, A.edge a b) =
      ∑ p ∈ folkmanBooleanTermSelectedPatterns t.val,
        ∑ q ∈ folkmanBooleanTermSelectedPatterns u.val,
          folkmanTuplePatternPairing A xs ys p q := by
  classical
  rw [folkmanBooleanTerm_evalSet_eq_selectedPatternUnion xs t.val,
    folkmanBooleanTerm_evalSet_eq_selectedPatternUnion ys u.val]
  exact folkmanTuplePatternPairing_biUnion A xs ys _ _
    (folkmanNonunitalTerm_zero_not_selected t)
    (folkmanNonunitalTerm_zero_not_selected u)

/-- Equal complete two-sort profiles preserve the pairing on every
pair of non-unital term evaluations (not merely the named generators). -/
theorem folkmanNonunitalTerm_pairing_of_profile_eq
    {A B : FolkmanAtomStructure}
    {nL nR : ℕ}
    (xsA : Fin nL → Finset (Fin A.leftCount))
    (ysA : Fin nR → Finset (Fin A.rightCount))
    (xsB : Fin nL → Finset (Fin B.leftCount))
    (ysB : Fin nR → Finset (Fin B.rightCount))
    (h : folkmanAtomTupleProfile A xsA ysA =
      folkmanAtomTupleProfile B xsB ysB)
    (t : FolkmanNonunitalTerm nL)
    (u : FolkmanNonunitalTerm nR) :
    (∑ a ∈ t.val.evalSet xsA,
      ∑ b ∈ u.val.evalSet ysA, A.edge a b) =
    (∑ a ∈ t.val.evalSet xsB,
      ∑ b ∈ u.val.evalSet ysB, B.edge a b) := by
  classical
  have hmatrix :
      ∀ p q,
        folkmanTuplePatternPairing A xsA ysA p q =
          folkmanTuplePatternPairing B xsB ysB p q := by
    intro p q
    exact congrFun (congrFun (congrArg Prod.snd h) p) q
  calc
    (∑ a ∈ t.val.evalSet xsA,
      ∑ b ∈ u.val.evalSet ysA, A.edge a b) =
      ∑ p ∈ folkmanBooleanTermSelectedPatterns t.val,
        ∑ q ∈ folkmanBooleanTermSelectedPatterns u.val,
          folkmanTuplePatternPairing A xsA ysA p q :=
      folkmanNonunitalTerm_pairing_eq_profile_sum A xsA ysA t u
    _ = ∑ p ∈ folkmanBooleanTermSelectedPatterns t.val,
          ∑ q ∈ folkmanBooleanTermSelectedPatterns u.val,
            folkmanTuplePatternPairing B xsB ysB p q := by
        apply Finset.sum_congr rfl
        intro p hp
        apply Finset.sum_congr rfl
        intro q hq
        exact hmatrix p q
    _ = (∑ a ∈ t.val.evalSet xsB,
          ∑ b ∈ u.val.evalSet ysB, B.edge a b) :=
      (folkmanNonunitalTerm_pairing_eq_profile_sum B xsB ysB t u).symm

end SuccessorTree.NonPrecompact
