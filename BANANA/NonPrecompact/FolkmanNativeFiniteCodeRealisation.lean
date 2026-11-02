import BANANA.NonPrecompact.FolkmanNativeFiniteClassInterface

/-!
# Native realisations of the countable Folkman atom-code family

Every finite atom code is realised by actual finite Boolean rings, not
merely by sets of atom labels. Conversely, every finite native pairing is
isomorphic to its realisation in the original two-sorted language.

The underlying rings have units, but the language does not name them and
embeddings are still non-unital. A bijective ring isomorphism necessarily
preserves the unit; using `RingEquiv` here adds no condition on embeddings.

This supplies explicit native representatives and arbitrarily large native
objects. It does not construct the countable homogeneous limit, nor prove
that an arbitrary finite non-unital subring has its own Boolean-ring unit.
This new source requires an exact-head Lean build before validation.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical symmDiff BigOperators

local instance folkmanAsBoolAlgFiniteForCodeRealisation
    (α : Type*) [Fintype α] : Fintype (AsBoolAlg α) :=
  Fintype.ofEquiv α toBoolAlg

/-- An actual finite Boolean ring on the subsets of `Fin n`.
For `n = 0` this is the one-element zero ring. -/
abbrev FolkmanNativeCodeRing (n : ℕ) := AsBoolRing (Finset (Fin n))

noncomputable instance folkmanNativeCodeRingFintype (n : ℕ) :
    Fintype (FolkmanNativeCodeRing n) :=
  Fintype.ofEquiv (Finset (Fin n)) toBoolRing

/-- Finite sums into F₂ are additive under symmetric difference.
The intersection contributions cancel, including for empty atom types. -/
theorem folkmanNativeCode_sum_symmDiff
    {I : Type*} [Fintype I] [DecidableEq I]
    (w : I → F2) (s t : Finset I) :
    (∑ i ∈ symmDiff s t, w i) =
      (∑ i ∈ s, w i) + ∑ i ∈ t, w i := by
  classical
  have hdouble : ∀ z : F2, z + z = 0 := by decide
  have hsum (u : Finset I) :
      (∑ i ∈ u, w i) = ∑ i : I, if i ∈ u then w i else 0 := by
    have hu : Finset.univ.filter (fun i : I => i ∈ u) = u := by
      ext i
      simp
    calc
      (∑ i ∈ u, w i) =
          ∑ i ∈ Finset.univ.filter (fun i : I => i ∈ u), w i := by
            rw [hu]
      _ = ∑ i : I, if i ∈ u then w i else 0 := by
        rw [Finset.sum_filter]
  rw [hsum (symmDiff s t), hsum s, hsum t, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;>
    simp [Finset.mem_symmDiff, hs, ht, hdouble]

/-- Realise any atom matrix as a bilinear pairing on two native finite
Boolean rings. Both sorts may be zero rings. -/
noncomputable def folkmanNativeCodeRealisation (A : FolkmanAtomStructure) :
    FolkmanNativeFinitePairing
      (FolkmanNativeCodeRing A.leftCount)
      (FolkmanNativeCodeRing A.rightCount) where
  pairing := fun x y => ∑ i ∈ ofBoolRing x, ∑ j ∈ ofBoolRing y, A.edge i j
  add_left := by
    intro x x' y
    change (∑ i ∈ symmDiff (ofBoolRing x) (ofBoolRing x'),
        ∑ j ∈ ofBoolRing y, A.edge i j) =
      (∑ i ∈ ofBoolRing x, ∑ j ∈ ofBoolRing y, A.edge i j) +
        ∑ i ∈ ofBoolRing x', ∑ j ∈ ofBoolRing y, A.edge i j
    exact folkmanNativeCode_sum_symmDiff
      (fun i => ∑ j ∈ ofBoolRing y, A.edge i j) _ _
  add_right := by
    intro x y y'
    change (∑ i ∈ ofBoolRing x,
        ∑ j ∈ symmDiff (ofBoolRing y) (ofBoolRing y'), A.edge i j) =
      (∑ i ∈ ofBoolRing x, ∑ j ∈ ofBoolRing y, A.edge i j) +
        ∑ i ∈ ofBoolRing x, ∑ j ∈ ofBoolRing y', A.edge i j
    simp_rw [folkmanNativeCode_sum_symmDiff]
    rw [Finset.sum_add_distrib]

/-- Realisation retains every specified atom-to-atom pairing value. -/
theorem folkmanNativeCodeRealisation_singletons (A : FolkmanAtomStructure)
    (i : Fin A.leftCount) (j : Fin A.rightCount) :
    (folkmanNativeCodeRealisation A).pairing
      (toBoolRing {i}) (toBoolRing {j}) = A.edge i j := by
  simp [folkmanNativeCodeRealisation]

/-- The finite atom-coordinate bijection is an actual ring isomorphism.
This concerns object isomorphisms, not the non-unital embedding convention. -/
noncomputable def folkmanNativeFiniteCodeRingEquiv
    (α : Type*) [BooleanRing α] [Fintype α] :
    α ≃+* FolkmanNativeCodeRing
      (Fintype.card (PrebananaAbstractAtoms (AsBoolAlg α))) where
  toEquiv := (folkmanNativeFiniteRingCodeEquiv α).trans toBoolRing
  map_mul' := by
    intro x y
    change toBoolRing (folkmanNativeFiniteRingCodeEquiv α (x * y)) =
      toBoolRing (folkmanNativeFiniteRingCodeEquiv α x ∩
        folkmanNativeFiniteRingCodeEquiv α y)
    exact congrArg toBoolRing (folkmanNativeFiniteRingCode_mul α x y)
  map_add' := by
    intro x y
    change toBoolRing (folkmanNativeFiniteRingCodeEquiv α (x + y)) =
      toBoolRing (symmDiff (folkmanNativeFiniteRingCodeEquiv α x)
        (folkmanNativeFiniteRingCodeEquiv α y))
    exact congrArg toBoolRing (folkmanNativeFiniteRingCode_add α x y)

/-- Isomorphism in the two-sorted native ring language, including the
original cross-pairing on all elements of both sorts. -/
structure FolkmanNativeFinitePairingIso
    {L R L' R' : Type*}
    [BooleanRing L] [BooleanRing R]
    [BooleanRing L'] [BooleanRing R']
    (P : FolkmanNativeFinitePairing L R)
    (Q : FolkmanNativeFinitePairing L' R') where
  left : L ≃+* L'
  right : R ≃+* R'
  preserves_pairing : ∀ x y, Q.pairing (left x) (right y) = P.pairing x y

/-- Every finite native object is isomorphic to the native realisation
of its atom code, in both ring operations and the entire cross-pairing. -/
noncomputable def folkmanNativeFiniteCodeIso
    {L R : Type*}
    [BooleanRing L] [Fintype L]
    [BooleanRing R] [Fintype R]
    (P : FolkmanNativeFinitePairing L R) :
    FolkmanNativeFinitePairingIso P
      (folkmanNativeCodeRealisation (folkmanNativeFinCode P.pairing)) where
  left := folkmanNativeFiniteCodeRingEquiv L
  right := folkmanNativeFiniteCodeRingEquiv R
  preserves_pairing := by
    intro x y
    change (∑ i ∈ folkmanNativeFiniteRingCodeEquiv L x,
        ∑ j ∈ folkmanNativeFiniteRingCodeEquiv R y,
          (folkmanNativeFinCode P.pairing).edge i j) = P.pairing x y
    exact (folkmanNativeFinCode_pairing
      P.pairing P.add_left P.add_right x y).symm

/-- A countably indexed family of actual native objects represents every
finite native Folkman isomorphism type. No uniqueness of codes is claimed:
renumbering atoms can change a code without changing its isomorphism type. -/
theorem folkmanNativeFinite_countable_native_representatives
    {L R : Type*}
    [BooleanRing L] [Fintype L]
    [BooleanRing R] [Fintype R]
    (P : FolkmanNativeFinitePairing L R) :
    Countable FolkmanAtomStructure ∧
      ∃ A : FolkmanAtomStructure,
        Nonempty (FolkmanNativeFinitePairingIso P
          (folkmanNativeCodeRealisation A)) := by
  exact ⟨inferInstance, folkmanNativeFinCode P.pairing,
    ⟨folkmanNativeFiniteCodeIso P⟩⟩

/-- Distinct singleton subsets are distinct elements of the native ring. -/
noncomputable def folkmanNativeCodeSingleton (n : ℕ) :
    Fin n ↪ FolkmanNativeCodeRing n where
  toFun := fun i => toBoolRing {i}
  inj' := by
    intro i j h
    have hs : ({i} : Finset (Fin n)) = {j} := congrArg ofBoolRing h
    have hi : i ∈ ({j} : Finset (Fin n)) := hs ▸ Finset.mem_singleton_self i
    simpa only [Finset.mem_singleton] using hi

/-- A lower bound on the number of actual ring elements, not atom codes. -/
theorem folkmanNativeCodeRing_card_ge (n : ℕ) :
    n ≤ Fintype.card (FolkmanNativeCodeRing n) := by
  have h := Fintype.card_le_of_injective
    (folkmanNativeCodeSingleton n) (folkmanNativeCodeSingleton n).injective
  simpa only [Fintype.card_fin] using h

/-- Native finite Folkman objects have arbitrarily large carriers in both
sorts. The witnesses have zero pairing and require no non-degeneracy. -/
theorem folkmanNativeFinite_native_objects_unbounded (n : ℕ) :
    ∃ P : FolkmanNativeFinitePairing
        (FolkmanNativeCodeRing (n + 1)) (FolkmanNativeCodeRing (n + 1)),
      n < Fintype.card (FolkmanNativeCodeRing (n + 1)) ∧
        n < Fintype.card (FolkmanNativeCodeRing (n + 1)) := by
  have hcard : n < Fintype.card (FolkmanNativeCodeRing (n + 1)) :=
    lt_of_lt_of_le (Nat.lt_succ_self n) (folkmanNativeCodeRing_card_ge (n + 1))
  exact ⟨folkmanNativeCodeRealisation
    (FolkmanAtomStructure.zeroPairing (n + 1) (n + 1)), hcard, hcard⟩

end SuccessorTree.NonPrecompact
