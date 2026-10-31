import BANANA.NonPrecompact.FolkmanTupleProfilesTransport

/-!
# Invariance of the full Folkman tuple profile under non-unital embeddings

An actual FolkmanAtomEmbedding preserves the F₂ pairing on every
source atom pair, expressed by its integer incidence-count parity.

For a *nonzero* tuple signature, the atoms with that signature in
the target are exactly the disjoint union of the owner fibres of
source atoms carrying the same signature.  The pairing on these
unions is therefore the sum of the source pairing values.

The all-zero signature, representing atoms outside the generated
non-unital ring, is assigned pairing value zero and omitted from
the realised pattern sets.  The resulting complete finite profile
is preserved on both sorts.

This does NOT yet prove that two equal profiles yield isomorphic
generated substructures or an automorphism of the countable limit.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical BigOperators

/-- For a nonzero signature, its entire target pattern fibre is
the union of the owner fibres of the corresponding source atoms.
No atom from an unowned target component can contribute. -/
theorem folkmanTuplePatternFiber_ownerImage_eq
    {n m k : ℕ}
    (owner : Fin m → Option (Fin n))
    (xs : Fin k → Finset (Fin n))
    (p : Fin k → Bool)
    (hp : p ≠ folkmanZeroTuplePattern k) :
    folkmanTuplePatternFiber (folkmanTupleOwnerImage owner xs) p =
      (folkmanTuplePatternFiber xs p).biUnion (folkmanFiber owner) := by
  classical
  ext b
  simp only [folkmanTuplePatternFiber,
    Finset.mem_filter, Finset.mem_univ, true_and]
  cases hown : owner b with
  | none =>
      have hz :=
        folkmanTupleOwnerImage_signature_none owner xs b hown
      constructor
      · intro hsig
        exact (hp (hsig.symm.trans hz)).elim
      · intro hb
        obtain ⟨a, _, hfiber⟩ := Finset.mem_biUnion.mp hb
        have hown' : owner b = some a :=
          (Finset.mem_filter.mp hfiber).2
        rw [hown] at hown'
        cases hown'
  | some a =>
      have heq :=
        folkmanTupleOwnerImage_signature_some owner xs b a hown
      constructor
      · intro hb
        apply Finset.mem_biUnion.mpr
        refine ⟨a, ?_, ?_⟩
        · exact Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, heq.symm.trans hb⟩
        · simp [folkmanFiber, hown]
      · intro hb
        obtain ⟨a', ha', hfiber⟩ := Finset.mem_biUnion.mp hb
        have hown' : owner b = some a' :=
          (Finset.mem_filter.mp hfiber).2
        have ha : a' = a := Option.some.inj (hown'.symm.trans hown)
        subst a'
        have hs : folkmanAtomTupleSignature xs a = p :=
          (Finset.mem_filter.mp ha').2
        exact heq.trans hs

/-- Ordinary Folkman incident-edge counts reduce modulo two to
the bilinear matrix sum. -/
theorem folkmanTuple_edgeCount_cast
    (A : FolkmanAtomStructure)
    (S : Finset (Fin A.leftCount))
    (T : Finset (Fin A.rightCount)) :
    (folkmanEdgeCount A.edge S T : F2) =
      ∑ a ∈ S, ∑ b ∈ T, A.edge a b := by
  classical
  simp only [folkmanEdgeCount, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rcases f2_eq_zero_or_one (A.edge a b) with hzero | hone
  · simp [hzero]
  · simp [hone]

/-- Pairing on unions of owner fibres agrees with the source
matrix pairing: this is the bilinear content of FolkmanAtomEmbedding. -/
theorem folkmanTupleOwnerPairing_sum
    {A B : FolkmanAtomStructure}
    (f : FolkmanAtomEmbedding A B)
    (S : Finset (Fin A.leftCount))
    (T : Finset (Fin A.rightCount)) :
    (∑ x ∈ S.biUnion (folkmanFiber f.leftOwner),
      ∑ y ∈ T.biUnion (folkmanFiber f.rightOwner),
        B.edge x y) =
      ∑ a ∈ S, ∑ b ∈ T, A.edge a b := by
  classical
  calc
    (∑ x ∈ S.biUnion (folkmanFiber f.leftOwner),
      ∑ y ∈ T.biUnion (folkmanFiber f.rightOwner),
        B.edge x y) =
      (folkmanEdgeCount B.edge
        (S.biUnion (folkmanFiber f.leftOwner))
        (T.biUnion (folkmanFiber f.rightOwner)) : F2) :=
          (folkmanTuple_edgeCount_cast B _ _).symm
    _ = ∑ a ∈ S, ∑ b ∈ T,
          (folkmanEdgeCount B.edge
            (folkmanFiber f.leftOwner a)
            (folkmanFiber f.rightOwner b) : F2) := by
      rw [folkmanEdgeCount_biUnion_left, Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro a ha
      rw [folkmanEdgeCount_biUnion_right, Nat.cast_sum]
    _ = ∑ a ∈ S, ∑ b ∈ T, A.edge a b := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      exact f.pairing_parity a b

/-- Every original finite tuple pairing-profile value survives
a non-unital Folkman atom embedding, including both zero-ring cases. -/
theorem folkmanTuplePatternPairing_ownerImage_eq
    {A B : FolkmanAtomStructure}
    (f : FolkmanAtomEmbedding A B)
    {nL nR : ℕ}
    (xs : Fin nL → Finset (Fin A.leftCount))
    (ys : Fin nR → Finset (Fin A.rightCount))
    (p : Fin nL → Bool) (q : Fin nR → Bool) :
    folkmanTuplePatternPairing B
      (folkmanTupleOwnerImage f.leftOwner xs)
      (folkmanTupleOwnerImage f.rightOwner ys) p q =
      folkmanTuplePatternPairing A xs ys p q := by
  classical
  by_cases hp : p = folkmanZeroTuplePattern nL
  · subst p
    simp [folkmanTuplePatternPairing]
  by_cases hq : q = folkmanZeroTuplePattern nR
  · subst q
    simp [folkmanTuplePatternPairing]
  unfold folkmanTuplePatternPairing
  simp only [hp, hq, false_or, or_false, if_false]
  rw [folkmanTuplePatternFiber_ownerImage_eq
        f.leftOwner xs p hp,
      folkmanTuplePatternFiber_ownerImage_eq
        f.rightOwner ys q hq]
  exact folkmanTupleOwnerPairing_sum f _ _

/-- The full finite Folkman two-sort profile is embedding-invariant.
This combines nonzero pattern support with the cross-pairing matrix. -/
theorem FolkmanAtomEmbedding.tupleProfile_preserved
    {A B : FolkmanAtomStructure}
    (f : FolkmanAtomEmbedding A B)
    {nL nR : ℕ}
    (xs : Fin nL → Finset (Fin A.leftCount))
    (ys : Fin nR → Finset (Fin A.rightCount)) :
    folkmanAtomTupleProfile B
      (folkmanTupleOwnerImage f.leftOwner xs)
      (folkmanTupleOwnerImage f.rightOwner ys) =
      folkmanAtomTupleProfile A xs ys := by
  classical
  apply Prod.ext
  · apply Prod.ext
    · exact f.leftTupleNonzeroPatterns_eq xs
    · exact f.rightTupleNonzeroPatterns_eq ys
  · funext p q
    exact folkmanTuplePatternPairing_ownerImage_eq f xs ys p q

end SuccessorTree.NonPrecompact
