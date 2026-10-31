import BANANA.NonPrecompact.FolkmanTupleProfiles

/-!
# Nonzero tuple patterns are invariant under partial atom owners

Every injective non-unital Boolean-ring embedding is represented by a
partial owner map on ambient atoms, with nonempty fibres above each
source atom.  Unowned target atoms have the zero tuple signature.

Consequently the nonzero membership patterns of a tuple are exactly
the same before and after the embedding.  This is the key difference
between the non-unital Folkman class and unital pre-BANANA.

The lemma is generic in the atom sets and reusable for both sorts.
It does not claim classification of tuples up to automorphisms.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical

/-- Extend a finite tuple of atom subsets by disjoint owner fibres. -/
noncomputable def folkmanTupleOwnerImage
    {n m k : ℕ}
    (owner : Fin m → Option (Fin n))
    (xs : Fin k → Finset (Fin n)) :
    Fin k → Finset (Fin m) := by
  classical
  exact fun i => (xs i).biUnion (folkmanFiber owner)

/-- A target atom owned by a source atom has exactly the source
atom's membership bits in every coordinate of the tuple. -/
theorem folkmanTupleOwnerImage_mem_some
    {n m k : ℕ}
    (owner : Fin m → Option (Fin n))
    (xs : Fin k → Finset (Fin n))
    (b : Fin m) (a : Fin n)
    (h : owner b = some a) (i : Fin k) :
    b ∈ folkmanTupleOwnerImage owner xs i ↔ a ∈ xs i := by
  classical
  change b ∈ (xs i).biUnion (folkmanFiber owner) ↔ a ∈ xs i
  constructor
  · intro hb
    obtain ⟨a', ha', hb'⟩ := Finset.mem_biUnion.mp hb
    have hown : owner b = some a' :=
      (Finset.mem_filter.mp hb').2
    have ha'a : a' = a := Option.some.inj (hown.symm.trans h)
    exact ha'a ▸ ha'
  · intro ha
    exact Finset.mem_biUnion.mpr
      ⟨a, ha, by simp [folkmanFiber, h]⟩

/-- Unowned target atoms belong to none of the embedded tuple entries. -/
theorem folkmanTupleOwnerImage_not_mem_none
    {n m k : ℕ}
    (owner : Fin m → Option (Fin n))
    (xs : Fin k → Finset (Fin n))
    (b : Fin m)
    (h : owner b = none) (i : Fin k) :
    b ∉ folkmanTupleOwnerImage owner xs i := by
  classical
  intro hb
  change b ∈ (xs i).biUnion (folkmanFiber owner) at hb
  obtain ⟨a, _, hb'⟩ := Finset.mem_biUnion.mp hb
  have hown : owner b = some a := (Finset.mem_filter.mp hb').2
  rw [h] at hown
  cases hown

theorem folkmanTupleOwnerImage_signature_some
    {n m k : ℕ}
    (owner : Fin m → Option (Fin n))
    (xs : Fin k → Finset (Fin n))
    (b : Fin m) (a : Fin n) (h : owner b = some a) :
    folkmanAtomTupleSignature (folkmanTupleOwnerImage owner xs) b =
      folkmanAtomTupleSignature xs a := by
  classical
  funext i
  have hmem := folkmanTupleOwnerImage_mem_some owner xs b a h i
  by_cases ha : a ∈ xs i
  · have hb : b ∈ folkmanTupleOwnerImage owner xs i := hmem.mpr ha
    simp [folkmanAtomTupleSignature, hb, ha]
  · have hb : b ∉ folkmanTupleOwnerImage owner xs i :=
      fun hx => ha (hmem.mp hx)
    simp [folkmanAtomTupleSignature, hb, ha]

theorem folkmanTupleOwnerImage_signature_none
    {n m k : ℕ}
    (owner : Fin m → Option (Fin n))
    (xs : Fin k → Finset (Fin n))
    (b : Fin m) (h : owner b = none) :
    folkmanAtomTupleSignature (folkmanTupleOwnerImage owner xs) b =
      folkmanZeroTuplePattern k := by
  classical
  funext i
  have hb := folkmanTupleOwnerImage_not_mem_none owner xs b h i
  simp [folkmanAtomTupleSignature, folkmanZeroTuplePattern, hb]

/-- Nonzero tuple membership signatures are exactly preserved by a
surjective-to-source partial atom owner, even if the target has extra
unowned atoms.  This is valid when either atom type is empty. -/
theorem folkmanTupleNonzeroPatterns_ownerImage_eq
    {n m k : ℕ}
    (owner : Fin m → Option (Fin n))
    (hsurj : ∀ a : Fin n, ∃ b : Fin m, owner b = some a)
    (xs : Fin k → Finset (Fin n)) :
    folkmanTupleNonzeroPatterns (folkmanTupleOwnerImage owner xs) =
      folkmanTupleNonzeroPatterns xs := by
  classical
  apply Finset.ext
  intro p
  unfold folkmanTupleNonzeroPatterns
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hp, hpnonzero⟩
    obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hp
    cases hown : owner b with
    | none =>
        have hz :=
          folkmanTupleOwnerImage_signature_none owner xs b hown
        rw [hz] at hb
        exact (hpnonzero hb.symm).elim
    | some a =>
        have heq :=
          folkmanTupleOwnerImage_signature_some owner xs b a hown
        refine ⟨Finset.mem_image.mpr ?_, hpnonzero⟩
        exact ⟨a, Finset.mem_univ _, heq.symm.trans hb⟩
  · rintro ⟨hp, hpnonzero⟩
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hp
    obtain ⟨b, hb⟩ := hsurj a
    have heq :=
      folkmanTupleOwnerImage_signature_some owner xs b a hb
    refine ⟨Finset.mem_image.mpr ?_, hpnonzero⟩
    exact ⟨b, Finset.mem_univ _, heq.trans ha⟩

end SuccessorTree.NonPrecompact
